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
% DateTime   : Thu Dec  3 13:21:13 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 142 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 496 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(resolution,[],[f108,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f50,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f48,f26,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f26,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f108,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f107,f99])).

fof(f99,plain,(
    k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f87,plain,(
    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f64,f77])).

fof(f77,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(forward_demodulation,[],[f51,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_subset_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f26,f39])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f64,plain,(
    r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f31,f28,f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
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
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ~ r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f91,f42])).

fof(f91,plain,(
    k1_xboole_0 != sK2(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f89,f66])).

fof(f66,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f89,plain,(
    sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f77])).

fof(f67,plain,(
    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f31,f28,f27,f48,f54,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f30,f40,f48,f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (21955)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (21960)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (21958)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (21961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.53  % (21966)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.54  % (21972)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.54  % (21963)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.54  % (21959)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.54  % (21982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.54  % (21959)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f113,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(resolution,[],[f108,f59])).
% 1.24/0.54  fof(f59,plain,(
% 1.24/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f50,f45])).
% 1.24/0.54  fof(f45,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.54  fof(f50,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f48,f26,f39])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    v1_xboole_0(sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.24/0.54    inference(flattening,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f13])).
% 1.24/0.54  fof(f13,negated_conjecture,(
% 1.24/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.24/0.54    inference(negated_conjecture,[],[f12])).
% 1.24/0.54  fof(f12,conjecture,(
% 1.24/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 1.24/0.54  fof(f48,plain,(
% 1.24/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.24/0.54  fof(f108,plain,(
% 1.24/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.24/0.54    inference(forward_demodulation,[],[f107,f99])).
% 1.24/0.54  fof(f99,plain,(
% 1.24/0.54    k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f87,f42])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.24/0.54    inference(ennf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.24/0.54  fof(f87,plain,(
% 1.24/0.54    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 1.24/0.54    inference(backward_demodulation,[],[f64,f77])).
% 1.24/0.54  fof(f77,plain,(
% 1.24/0.54    k1_xboole_0 = sK1),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f61,f42])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f53,f45])).
% 1.24/0.54  fof(f53,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 1.24/0.54    inference(forward_demodulation,[],[f51,f43])).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.24/0.54  fof(f51,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,k2_subset_1(sK1))) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f49,f26,f39])).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.24/0.54  fof(f64,plain,(
% 1.24/0.54    r1_tarski(sK2(sK0,sK1),sK1)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f31,f28,f27,f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f17])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f11])).
% 1.24/0.54  fof(f11,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ~v2_tex_2(sK1,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    l1_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f107,plain,(
% 1.24/0.54    ~r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f91,f42])).
% 1.24/0.54  fof(f91,plain,(
% 1.24/0.54    k1_xboole_0 != sK2(sK0,k1_xboole_0)),
% 1.24/0.54    inference(forward_demodulation,[],[f89,f66])).
% 1.24/0.54  fof(f66,plain,(
% 1.24/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,X0) = X0) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f27,f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.24/0.54  fof(f89,plain,(
% 1.24/0.54    sK2(sK0,k1_xboole_0) != k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 1.24/0.54    inference(backward_demodulation,[],[f67,f77])).
% 1.24/0.54  fof(f67,plain,(
% 1.24/0.54    sK2(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f31,f28,f27,f48,f54,f32])).
% 1.24/0.54  fof(f32,plain,(
% 1.24/0.54    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f17])).
% 1.24/0.54  fof(f54,plain,(
% 1.24/0.54    v4_pre_topc(k1_xboole_0,sK0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f30,f40,f48,f31,f38])).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f18])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,axiom,(
% 1.24/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.24/0.54  fof(f40,plain,(
% 1.24/0.54    v1_xboole_0(k1_xboole_0)),
% 1.24/0.54    inference(cnf_transformation,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    v1_xboole_0(k1_xboole_0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    v2_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (21959)------------------------------
% 1.24/0.54  % (21959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (21959)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (21959)Memory used [KB]: 6268
% 1.24/0.54  % (21959)Time elapsed: 0.125 s
% 1.24/0.54  % (21959)------------------------------
% 1.24/0.54  % (21959)------------------------------
% 1.24/0.54  % (21957)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.54  % (21954)Success in time 0.177 s
%------------------------------------------------------------------------------
