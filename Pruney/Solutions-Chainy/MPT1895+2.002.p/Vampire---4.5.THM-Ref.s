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
% DateTime   : Thu Dec  3 13:22:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 225 expanded)
%              Number of leaves         :    8 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  200 (1259 expanded)
%              Number of equality atoms :   32 ( 210 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18659)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f62])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f25,f57])).

fof(f57,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f50,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1))
    & v3_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,X1))
          & v3_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,X1))
        & v3_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1))
      & v3_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
             => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
           => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tex_2)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f73,f57])).

fof(f73,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f71,f70])).

fof(f70,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f69,f62])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f68,f57])).

fof(f68,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f67,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f23])).

fof(f23,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f24])).

fof(f64,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f63,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tex_2)).

fof(f63,plain,(
    k3_tarski(a_2_0_tex_2(sK0,sK1)) != k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f27,f57])).

fof(f27,plain,(
    u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f56,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f55,plain,
    ( v1_tops_1(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f54,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f53,f23])).

fof(f53,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f52,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).

fof(f26,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (18650)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (18652)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (18652)Refutation not found, incomplete strategy% (18652)------------------------------
% 0.20/0.49  % (18652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18652)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18652)Memory used [KB]: 10490
% 0.20/0.49  % (18652)Time elapsed: 0.071 s
% 0.20/0.49  % (18652)------------------------------
% 0.20/0.49  % (18652)------------------------------
% 0.20/0.49  % (18661)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (18661)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (18659)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f25,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f50,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f24,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    (u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1)) & v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,X1)) & v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X1] : (u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,X1)) & v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1)) & v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1)) & v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tex_2)).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.50    inference(forward_demodulation,[],[f73,f57])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f24])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f62])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f68,f57])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f67,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f65,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    v3_tdlat_3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f64,f24])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(superposition,[],[f63,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tex_2)).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    k3_tarski(a_2_0_tex_2(sK0,sK1)) != k2_struct_0(sK0)),
% 0.20/0.50    inference(backward_demodulation,[],[f27,f57])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k3_tarski(a_2_0_tex_2(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f56,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f55,f21])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f54,f22])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f53,f23])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f52,f24])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f51,f25])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) => v1_tops_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (18661)------------------------------
% 0.20/0.50  % (18661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18661)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (18661)Memory used [KB]: 1663
% 0.20/0.50  % (18661)Time elapsed: 0.072 s
% 0.20/0.50  % (18661)------------------------------
% 0.20/0.50  % (18661)------------------------------
% 0.20/0.50  % (18662)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (18646)Success in time 0.134 s
%------------------------------------------------------------------------------
