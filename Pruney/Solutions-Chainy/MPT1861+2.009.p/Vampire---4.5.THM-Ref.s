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
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 100 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 ( 334 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f64,f79,f87,f92,f115,f118])).

fof(f118,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f90,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f90,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_6
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f115,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_5
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f81,f62,f35,f89])).

fof(f35,plain,
    ( spl3_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_4
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f63,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f63,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f87,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f80,f62,f32,f84])).

fof(f32,plain,
    ( spl3_1
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f63,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(resolution,[],[f68,f24])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_3 ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f65,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_3 ),
    inference(resolution,[],[f60,f26])).

% (2520)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (2525)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (2515)Refutation not found, incomplete strategy% (2515)------------------------------
% (2515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2515)Termination reason: Refutation not found, incomplete strategy

% (2515)Memory used [KB]: 10618
% (2515)Time elapsed: 0.118 s
% (2515)------------------------------
% (2515)------------------------------
% (2522)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (2526)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_3
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f57,f62,f59])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(global_subsumption,[],[f22,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f23,f48])).

fof(f48,plain,(
    ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f20,f45])).

fof(f45,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(resolution,[],[f28,f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f20,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f18,f35,f32])).

fof(f18,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (2519)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (2519)Refutation not found, incomplete strategy% (2519)------------------------------
% 0.20/0.47  % (2519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (2519)Memory used [KB]: 10618
% 0.20/0.47  % (2519)Time elapsed: 0.051 s
% 0.20/0.47  % (2519)------------------------------
% 0.20/0.47  % (2519)------------------------------
% 0.20/0.47  % (2527)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (2513)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.53  % (2529)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.53  % (2509)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.53  % (2529)Refutation not found, incomplete strategy% (2529)------------------------------
% 0.20/0.53  % (2529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2529)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2529)Memory used [KB]: 6140
% 0.20/0.53  % (2529)Time elapsed: 0.088 s
% 0.20/0.53  % (2529)------------------------------
% 0.20/0.53  % (2529)------------------------------
% 0.20/0.53  % (2521)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.53  % (2511)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.54  % (2515)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.54  % (2516)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (2514)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.54  % (2524)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.54  % (2531)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.54  % (2510)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (2527)Refutation not found, incomplete strategy% (2527)------------------------------
% 0.20/0.54  % (2527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2527)Memory used [KB]: 6140
% 0.20/0.54  % (2527)Time elapsed: 0.126 s
% 0.20/0.54  % (2527)------------------------------
% 0.20/0.54  % (2527)------------------------------
% 0.20/0.55  % (2523)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.55  % (2512)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.55  % (2521)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (2532)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.55  % (2528)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f37,f64,f79,f87,f92,f115,f118])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    spl3_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    $false | spl3_6),
% 0.20/0.55    inference(resolution,[],[f90,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl3_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    spl3_6 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    spl3_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    $false | spl3_5),
% 0.20/0.55    inference(resolution,[],[f85,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.55    inference(superposition,[],[f24,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    spl3_5 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~spl3_6 | ~spl3_2 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f81,f62,f35,f89])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    spl3_2 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    spl3_4 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ~v2_tex_2(sK1,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~spl3_4),
% 0.20/0.55    inference(resolution,[],[f63,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.55    inference(negated_conjecture,[],[f8])).
% 0.20/0.55  fof(f8,conjecture,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0)) ) | ~spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f62])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ~spl3_5 | ~spl3_1 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f80,f62,f32,f84])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    spl3_1 <=> v2_tex_2(sK2,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ~v2_tex_2(sK2,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~spl3_4),
% 0.20/0.55    inference(resolution,[],[f63,f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    spl3_3),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    $false | spl3_3),
% 0.20/0.55    inference(resolution,[],[f69,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.55    inference(resolution,[],[f27,f21])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f68,f24])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f65,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f60,f26])).
% 0.20/0.56  % (2520)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.56  % (2525)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.56  % (2515)Refutation not found, incomplete strategy% (2515)------------------------------
% 0.20/0.56  % (2515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2515)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (2515)Memory used [KB]: 10618
% 0.20/0.56  % (2515)Time elapsed: 0.118 s
% 0.20/0.56  % (2515)------------------------------
% 0.20/0.56  % (2515)------------------------------
% 0.20/0.56  % (2522)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.56  % (2526)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl3_3 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ~spl3_3 | spl3_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f57,f62,f59])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.57    inference(global_subsumption,[],[f22,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.57    inference(resolution,[],[f23,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ~v2_tex_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.57    inference(backward_demodulation,[],[f20,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 0.20/0.57    inference(resolution,[],[f28,f19])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    l1_pre_topc(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    spl3_1 | spl3_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f18,f35,f32])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    v2_tex_2(sK1,sK0) | v2_tex_2(sK2,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (2521)------------------------------
% 0.20/0.57  % (2521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (2521)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (2521)Memory used [KB]: 10618
% 0.20/0.57  % (2521)Time elapsed: 0.145 s
% 0.20/0.57  % (2521)------------------------------
% 0.20/0.57  % (2521)------------------------------
% 0.20/0.57  % (2530)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.57  % (2508)Success in time 0.212 s
%------------------------------------------------------------------------------
