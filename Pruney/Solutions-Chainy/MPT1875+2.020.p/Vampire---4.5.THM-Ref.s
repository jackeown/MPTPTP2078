%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 184 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   23
%              Number of atoms          :  206 ( 886 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f69,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f27,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f40,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

% (5275)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (5277)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (5275)Refutation not found, incomplete strategy% (5275)------------------------------
% (5275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5275)Termination reason: Refutation not found, incomplete strategy

% (5275)Memory used [KB]: 6140
% (5275)Time elapsed: 0.125 s
% (5275)------------------------------
% (5275)------------------------------
% (5294)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (5272)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (5296)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (5286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (5290)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (5278)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (5296)Refutation not found, incomplete strategy% (5296)------------------------------
% (5296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5296)Termination reason: Refutation not found, incomplete strategy

% (5296)Memory used [KB]: 6268
% (5296)Time elapsed: 0.139 s
% (5296)------------------------------
% (5296)------------------------------
fof(f35,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f65,plain,(
    ~ v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f63,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

% (5285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f60,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,(
    ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f55,f29])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f54,plain,(
    ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f53,plain,
    ( ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,
    ( ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f48,f42])).

fof(f48,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2(sK1,X0),X0) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (5273)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (5279)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (5273)Refutation not found, incomplete strategy% (5273)------------------------------
% 0.21/0.51  % (5273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5279)Refutation not found, incomplete strategy% (5279)------------------------------
% 0.21/0.51  % (5279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5273)Memory used [KB]: 10746
% 0.21/0.51  % (5273)Time elapsed: 0.089 s
% 0.21/0.51  % (5273)------------------------------
% 0.21/0.51  % (5273)------------------------------
% 0.21/0.51  % (5279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5279)Memory used [KB]: 10618
% 0.21/0.51  % (5279)Time elapsed: 0.091 s
% 0.21/0.51  % (5279)------------------------------
% 0.21/0.51  % (5279)------------------------------
% 0.21/0.52  % (5274)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (5274)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    v1_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f65,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f40,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f32,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f35])).
% 0.21/0.53  % (5275)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (5277)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5275)Refutation not found, incomplete strategy% (5275)------------------------------
% 0.21/0.53  % (5275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5275)Memory used [KB]: 6140
% 0.21/0.53  % (5275)Time elapsed: 0.125 s
% 0.21/0.53  % (5275)------------------------------
% 0.21/0.53  % (5275)------------------------------
% 0.21/0.53  % (5294)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5272)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (5296)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (5290)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (5278)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (5296)Refutation not found, incomplete strategy% (5296)------------------------------
% 0.21/0.54  % (5296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5296)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5296)Memory used [KB]: 6268
% 0.21/0.54  % (5296)Time elapsed: 0.139 s
% 0.21/0.54  % (5296)------------------------------
% 0.21/0.54  % (5296)------------------------------
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f63,f42])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f60,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f45,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f44,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ~v2_tex_2(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(X1,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f33,f28])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  % (5285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(resolution,[],[f58,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),sK1)),
% 0.21/0.54    inference(resolution,[],[f55,f29])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),X0)) )),
% 0.21/0.54    inference(resolution,[],[f54,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f53,f25])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f52,f28])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f51,f27])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f48,f42])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f47,f43])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK1,X0),X0)) )),
% 0.21/0.54    inference(resolution,[],[f46,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (5274)------------------------------
% 0.21/0.54  % (5274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5274)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (5274)Memory used [KB]: 10746
% 0.21/0.54  % (5274)Time elapsed: 0.119 s
% 0.21/0.54  % (5274)------------------------------
% 0.21/0.54  % (5274)------------------------------
% 0.21/0.54  % (5270)Success in time 0.179 s
%------------------------------------------------------------------------------
