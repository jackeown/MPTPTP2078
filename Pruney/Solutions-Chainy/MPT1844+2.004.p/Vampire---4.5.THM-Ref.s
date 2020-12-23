%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 653 expanded)
%              Number of leaves         :    9 ( 123 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 (2102 expanded)
%              Number of equality atoms :   27 ( 171 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f86])).

fof(f86,plain,(
    k1_tarski(sK1) = k6_domain_1(k1_tarski(sK1),sK1) ),
    inference(backward_demodulation,[],[f70,f77])).

fof(f77,plain,(
    k2_struct_0(sK0) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f66,plain,(
    r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f25,f47])).

fof(f47,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

% (1555)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f43,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f42,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,
    ( k2_struct_0(sK0) = k1_tarski(sK1)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f73,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f71,plain,
    ( k2_struct_0(sK0) = k1_tarski(sK1)
    | ~ m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f63,f70])).

fof(f63,plain,
    ( ~ m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k6_domain_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

% (1557)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f22,plain,(
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

fof(f49,plain,(
    ~ v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f26,f47])).

fof(f26,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f113,plain,(
    k1_tarski(sK1) != k6_domain_1(k1_tarski(sK1),sK1) ),
    inference(resolution,[],[f91,f80])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f48,f77])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_tarski(sK1))
      | k1_tarski(sK1) != k6_domain_1(k1_tarski(sK1),X0) ) ),
    inference(forward_demodulation,[],[f84,f77])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_tarski(sK1))
      | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0) ) ),
    inference(backward_demodulation,[],[f62,f77])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f60,plain,(
    ~ v1_zfmisc_1(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( ~ v1_zfmisc_1(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f28,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,
    ( ~ v1_zfmisc_1(k2_struct_0(sK0))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f34,f47])).

fof(f34,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (1559)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (1565)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (1565)Refutation not found, incomplete strategy% (1565)------------------------------
% 0.20/0.49  % (1565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1565)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1565)Memory used [KB]: 10490
% 0.20/0.49  % (1565)Time elapsed: 0.068 s
% 0.20/0.49  % (1565)------------------------------
% 0.20/0.49  % (1565)------------------------------
% 0.20/0.51  % (1548)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (1550)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (1549)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (1558)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (1558)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f113,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    k1_tarski(sK1) = k6_domain_1(k1_tarski(sK1),sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f70,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    k2_struct_0(sK0) = k1_tarski(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f76,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f51,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f25,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f29,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  % (1555)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,k2_struct_0(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f43,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f42,f29])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f27,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k1_tarski(sK1) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f73,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k1_tarski(sK1)),
% 0.20/0.53    inference(forward_demodulation,[],[f71,f70])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k1_tarski(sK1) | ~m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f63,f70])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ~m1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k6_domain_1(k2_struct_0(sK0),sK1)),
% 0.20/0.53    inference(resolution,[],[f49,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  % (1557)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ~v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.20/0.53    inference(backward_demodulation,[],[f26,f47])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.53    inference(resolution,[],[f50,f48])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0)) )),
% 0.20/0.53    inference(resolution,[],[f43,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    k1_tarski(sK1) != k6_domain_1(k1_tarski(sK1),sK1)),
% 0.20/0.53    inference(resolution,[],[f91,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_tarski(sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f48,f77])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(sK1)) | k1_tarski(sK1) != k6_domain_1(k1_tarski(sK1),X0)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f84,f77])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(sK1)) | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0)) )),
% 0.20/0.53    inference(backward_demodulation,[],[f62,f77])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f61,f43])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | k2_struct_0(sK0) != k6_domain_1(k2_struct_0(sK0),X0)) )),
% 0.20/0.53    inference(resolution,[],[f60,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~v1_zfmisc_1(k2_struct_0(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f59,f29])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ~v1_zfmisc_1(k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f58,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ~v7_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ~v1_zfmisc_1(k2_struct_0(sK0)) | v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f34,f47])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (v7_struct_0(X0) | ~l1_struct_0(X0) | ~v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (1558)------------------------------
% 0.20/0.53  % (1558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1558)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (1558)Memory used [KB]: 1663
% 0.20/0.53  % (1558)Time elapsed: 0.031 s
% 0.20/0.53  % (1558)------------------------------
% 0.20/0.53  % (1558)------------------------------
% 0.20/0.53  % (1543)Success in time 0.172 s
%------------------------------------------------------------------------------
