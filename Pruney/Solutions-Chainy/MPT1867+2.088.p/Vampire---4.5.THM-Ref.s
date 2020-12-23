%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:18 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 143 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   19
%              Number of atoms          :  197 ( 504 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f56])).

fof(f56,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f31,f53])).

fof(f53,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f35,f29])).

fof(f29,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

% (28059)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (28047)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (28035)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (28035)Refutation not found, incomplete strategy% (28035)------------------------------
% (28035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28035)Termination reason: Refutation not found, incomplete strategy

% (28035)Memory used [KB]: 10618
% (28035)Time elapsed: 0.124 s
% (28035)------------------------------
% (28035)------------------------------
% (28034)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (28044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (28056)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (28045)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (28057)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (28060)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (28046)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (28052)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (28054)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (28051)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (28042)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (28041)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (28037)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (28055)Refutation not found, incomplete strategy% (28055)------------------------------
% (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28055)Termination reason: Refutation not found, incomplete strategy

% (28055)Memory used [KB]: 10746
% (28055)Time elapsed: 0.090 s
% (28055)------------------------------
% (28055)------------------------------
% (28038)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (28061)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (28041)Refutation not found, incomplete strategy% (28041)------------------------------
% (28041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28041)Termination reason: Refutation not found, incomplete strategy

% (28041)Memory used [KB]: 10746
% (28041)Time elapsed: 0.150 s
% (28041)------------------------------
% (28041)------------------------------
% (28054)Termination reason: Refutation not found, incomplete strategy

% (28054)Memory used [KB]: 1791
% (28054)Time elapsed: 0.132 s
% (28054)------------------------------
% (28054)------------------------------
% (28036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f31,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f206,plain,(
    v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f205,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f205,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f203,f108])).

fof(f108,plain,(
    k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f104,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f104,plain,(
    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f100,f34])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK2(sK0,X0),X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f203,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(superposition,[],[f200,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

% (28043)Refutation not found, incomplete strategy% (28043)------------------------------
% (28043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28043)Termination reason: Refutation not found, incomplete strategy

% (28043)Memory used [KB]: 10746
% (28043)Time elapsed: 0.137 s
% (28043)------------------------------
% (28043)------------------------------
fof(f200,plain,(
    ! [X3] :
      ( sK2(sK0,X3) != k1_setfam_1(k2_tarski(X3,k1_xboole_0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X3,sK0) ) ),
    inference(forward_demodulation,[],[f199,f66])).

fof(f66,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f199,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X3) != k9_subset_1(u1_struct_0(sK0),X3,k1_xboole_0)
      | v2_tex_2(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f196,f34])).

fof(f196,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X3) != k9_subset_1(u1_struct_0(sK0),X3,k1_xboole_0)
      | v2_tex_2(X3,sK0) ) ),
    inference(resolution,[],[f193,f157])).

fof(f157,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(resolution,[],[f156,f34])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(subsumption_resolution,[],[f155,f34])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(superposition,[],[f152,f68])).

fof(f68,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f61,f34])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f152,plain,(
    ! [X0,X1] :
      ( k1_tops_1(sK0,X0) != X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f151,f33])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(sK0,X1) != X1
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f150,f33])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(sK0,X1) != X1
      | v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1)
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (28039)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (28049)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.53  % (28048)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.53  % (28040)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (28033)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (28055)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.53  % (28039)Refutation found. Thanks to Tanya!
% 1.31/0.53  % SZS status Theorem for theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f207,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(subsumption_resolution,[],[f206,f56])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ~v2_tex_2(k1_xboole_0,sK0)),
% 1.31/0.53    inference(backward_demodulation,[],[f31,f53])).
% 1.31/0.53  fof(f53,plain,(
% 1.31/0.53    k1_xboole_0 = sK1),
% 1.31/0.53    inference(resolution,[],[f35,f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    v1_xboole_0(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.31/0.53    inference(pure_predicate_removal,[],[f14])).
% 1.31/0.53  fof(f14,negated_conjecture,(
% 1.31/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.31/0.53    inference(negated_conjecture,[],[f13])).
% 1.31/0.53  fof(f13,conjecture,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f20])).
% 1.31/0.54  % (28059)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (28047)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (28035)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (28035)Refutation not found, incomplete strategy% (28035)------------------------------
% 1.31/0.54  % (28035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (28035)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (28035)Memory used [KB]: 10618
% 1.31/0.54  % (28035)Time elapsed: 0.124 s
% 1.31/0.54  % (28035)------------------------------
% 1.31/0.54  % (28035)------------------------------
% 1.31/0.54  % (28034)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (28044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (28056)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.54  % (28045)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.54  % (28057)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.54  % (28060)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (28046)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  % (28052)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (28054)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.55  % (28051)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (28042)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% 1.42/0.55  % (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (28043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (28041)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (28037)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.55  % (28055)Refutation not found, incomplete strategy% (28055)------------------------------
% 1.42/0.55  % (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (28055)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (28055)Memory used [KB]: 10746
% 1.42/0.55  % (28055)Time elapsed: 0.090 s
% 1.42/0.55  % (28055)------------------------------
% 1.42/0.55  % (28055)------------------------------
% 1.42/0.55  % (28038)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.56  % (28061)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (28041)Refutation not found, incomplete strategy% (28041)------------------------------
% 1.42/0.56  % (28041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (28041)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (28041)Memory used [KB]: 10746
% 1.42/0.56  % (28041)Time elapsed: 0.150 s
% 1.42/0.56  % (28041)------------------------------
% 1.42/0.56  % (28041)------------------------------
% 1.42/0.56  % (28054)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (28054)Memory used [KB]: 1791
% 1.42/0.56  % (28054)Time elapsed: 0.132 s
% 1.42/0.56  % (28054)------------------------------
% 1.42/0.56  % (28054)------------------------------
% 1.42/0.56  % (28036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ~v2_tex_2(sK1,sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f206,plain,(
% 1.42/0.56    v2_tex_2(k1_xboole_0,sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f205,f34])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.42/0.56  fof(f205,plain,(
% 1.42/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_xboole_0,sK0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f203,f108])).
% 1.42/0.56  fof(f108,plain,(
% 1.42/0.56    k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 1.42/0.56    inference(resolution,[],[f104,f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f25])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.42/0.56    inference(ennf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.42/0.56  fof(f104,plain,(
% 1.42/0.56    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 1.42/0.56    inference(subsumption_resolution,[],[f102,f56])).
% 1.42/0.56  fof(f102,plain,(
% 1.42/0.56    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0)),
% 1.42/0.56    inference(resolution,[],[f100,f34])).
% 1.42/0.56  fof(f100,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f42,f33])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    l1_pre_topc(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f12])).
% 1.42/0.56  fof(f12,axiom,(
% 1.42/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 1.42/0.56  fof(f203,plain,(
% 1.42/0.56    k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_xboole_0,sK0)),
% 1.42/0.56    inference(superposition,[],[f200,f58])).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 1.42/0.56    inference(resolution,[],[f51,f44])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f47,f48])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.42/0.56  % (28043)Refutation not found, incomplete strategy% (28043)------------------------------
% 1.42/0.56  % (28043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (28043)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (28043)Memory used [KB]: 10746
% 1.42/0.56  % (28043)Time elapsed: 0.137 s
% 1.42/0.56  % (28043)------------------------------
% 1.42/0.56  % (28043)------------------------------
% 1.42/0.56  fof(f200,plain,(
% 1.42/0.56    ( ! [X3] : (sK2(sK0,X3) != k1_setfam_1(k2_tarski(X3,k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X3,sK0)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f199,f66])).
% 1.42/0.56  fof(f66,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k1_setfam_1(k2_tarski(X1,k1_xboole_0))) )),
% 1.42/0.56    inference(resolution,[],[f52,f34])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f49,f48])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f28,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.42/0.56  fof(f199,plain,(
% 1.42/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X3) != k9_subset_1(u1_struct_0(sK0),X3,k1_xboole_0) | v2_tex_2(X3,sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f196,f34])).
% 1.42/0.56  fof(f196,plain,(
% 1.42/0.56    ( ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X3) != k9_subset_1(u1_struct_0(sK0),X3,k1_xboole_0) | v2_tex_2(X3,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f193,f157])).
% 1.42/0.56  fof(f157,plain,(
% 1.42/0.56    v3_pre_topc(k1_xboole_0,sK0)),
% 1.42/0.56    inference(resolution,[],[f156,f34])).
% 1.42/0.56  fof(f156,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_xboole_0,sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f155,f34])).
% 1.42/0.56  fof(f155,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_xboole_0,sK0)) )),
% 1.42/0.56    inference(trivial_inequality_removal,[],[f154])).
% 1.42/0.56  fof(f154,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_xboole_0,sK0)) )),
% 1.42/0.56    inference(superposition,[],[f152,f68])).
% 1.42/0.56  fof(f68,plain,(
% 1.42/0.56    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 1.42/0.56    inference(resolution,[],[f63,f44])).
% 1.42/0.56  fof(f63,plain,(
% 1.42/0.56    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.42/0.56    inference(resolution,[],[f61,f34])).
% 1.42/0.56  fof(f61,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.42/0.56    inference(resolution,[],[f36,f33])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,axiom,(
% 1.42/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.42/0.56  fof(f152,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k1_tops_1(sK0,X0) != X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f151,f33])).
% 1.42/0.56  fof(f151,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(sK0,X1) != X1 | v3_pre_topc(X1,sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f150,f33])).
% 1.42/0.56  fof(f150,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(sK0,X1) != X1 | v3_pre_topc(X1,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f45,f32])).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    v2_pre_topc(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f27])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.56    inference(flattening,[],[f26])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f11])).
% 1.42/0.56  fof(f11,axiom,(
% 1.42/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.42/0.56  fof(f193,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X0) != k9_subset_1(u1_struct_0(sK0),X0,X1) | v2_tex_2(X0,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f37,f33])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f23])).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (28039)------------------------------
% 1.42/0.56  % (28039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (28039)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (28039)Memory used [KB]: 6396
% 1.42/0.56  % (28039)Time elapsed: 0.117 s
% 1.42/0.56  % (28039)------------------------------
% 1.42/0.56  % (28039)------------------------------
% 1.42/0.56  % (28032)Success in time 0.199 s
%------------------------------------------------------------------------------
