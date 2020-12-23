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
% DateTime   : Thu Dec  3 13:20:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 153 expanded)
%              Number of leaves         :    6 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 668 expanded)
%              Number of equality atoms :   45 ( 187 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f43])).

fof(f43,plain,(
    u1_pre_topc(sK0) != u1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f42,f26])).

fof(f26,plain,(
    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f25,f15])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ v2_tdlat_3(X1)
        & v2_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_tdlat_3(sK1)
      & v2_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(f25,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f42,plain,(
    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f41,f16])).

fof(f16,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f39,f19])).

fof(f19,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | v2_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f22,f35])).

fof(f35,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f33])).

fof(f33,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f31,f17])).

fof(f17,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f23,f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f22,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f17,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(resolution,[],[f44,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f40,f16])).

fof(f40,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f20,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.52  % (986)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (975)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (975)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (994)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f55,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    u1_pre_topc(sK0) != u1_pre_topc(sK1)),
% 0.22/0.53    inference(forward_demodulation,[],[f42,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f25,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f4])).
% 0.22/0.53  fof(f4,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f21,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    v2_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_tdlat_3(X0) | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (((v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))) & (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f41,f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f39,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ~v2_tdlat_3(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | v2_tdlat_3(sK1) | ~l1_pre_topc(sK1)),
% 0.22/0.53    inference(superposition,[],[f22,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.53    inference(superposition,[],[f31,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) )),
% 0.22/0.53    inference(resolution,[],[f29,f15])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 0.22/0.53    inference(resolution,[],[f23,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.22/0.53    inference(equality_resolution,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK1) = X1) )),
% 0.22/0.53    inference(superposition,[],[f45,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),
% 0.22/0.53    inference(backward_demodulation,[],[f17,f35])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) | u1_pre_topc(sK1) = X1) )),
% 0.22/0.53    inference(resolution,[],[f44,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    inference(subsumption_resolution,[],[f40,f16])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1)),
% 0.22/0.53    inference(superposition,[],[f20,f35])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (975)------------------------------
% 0.22/0.53  % (975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (975)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (975)Memory used [KB]: 6268
% 0.22/0.53  % (975)Time elapsed: 0.115 s
% 0.22/0.53  % (975)------------------------------
% 0.22/0.53  % (975)------------------------------
% 0.22/0.53  % (957)Success in time 0.168 s
%------------------------------------------------------------------------------
