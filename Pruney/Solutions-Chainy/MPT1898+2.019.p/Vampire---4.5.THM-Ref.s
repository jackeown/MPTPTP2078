%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 223 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  222 (1118 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f66])).

fof(f66,plain,(
    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f65,plain,
    ( v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f28,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,
    ( v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,
    ( v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f49])).

fof(f49,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f48,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f47,f29])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),sK2(u1_struct_0(X0))),X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f54,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0)
    | v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK1(X0,X1),X0)
            & r1_tarski(X1,sK1(X0,X1))
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK1(X0,X1),X0)
        & r1_tarski(X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f51,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f50,f26])).

fof(f50,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
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

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),sK2(u1_struct_0(X0))),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,sK2(X0)),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f72,plain,(
    ~ v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) ),
    inference(resolution,[],[f61,f30])).

fof(f30,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f59,plain,
    ( m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,
    ( m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,
    ( m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f53,f49])).

fof(f53,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0)
    | m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (7411)WARNING: option uwaf not known.
% 0.22/0.46  % (7411)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.46  % (7411)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f72,f66])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f65,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ~v2_struct_0(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f7])).
% 0.22/0.46  fof(f7,conjecture,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f64,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    v2_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f63,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    v3_tdlat_3(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f62,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    l1_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f54,f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f48,f26])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f47,f29])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ~l1_pre_topc(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f42,f27])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),sK2(u1_struct_0(X0))),X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(resolution,[],[f36,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0) | v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f51,f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(subsumption_resolution,[],[f50,f26])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f46,f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    l1_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f31,f29])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),sK2(u1_struct_0(X0))),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(resolution,[],[f41,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X0] : (v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,sK2(X0)),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(resolution,[],[f38,f37])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.46    inference(flattening,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    ~v3_tex_2(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),sK0)),
% 0.22/0.46    inference(resolution,[],[f61,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(subsumption_resolution,[],[f60,f26])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f59,f27])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f58,f28])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f57,f29])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f53,f49])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))),sK0) | m1_subset_1(sK1(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f51,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (7411)------------------------------
% 0.22/0.46  % (7411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (7411)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (7411)Memory used [KB]: 895
% 0.22/0.46  % (7411)Time elapsed: 0.047 s
% 0.22/0.46  % (7411)------------------------------
% 0.22/0.46  % (7411)------------------------------
% 0.22/0.47  % (7400)Success in time 0.108 s
%------------------------------------------------------------------------------
