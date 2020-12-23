%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 310 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f53])).

fof(f53,plain,(
    v1_xboole_0(sK1) ),
    inference(definition_unfolding,[],[f39,f28])).

fof(f28,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f113,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f83,f101])).

fof(f101,plain,(
    sK1 = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f74,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | sK1 = X0 ) ),
    inference(superposition,[],[f54,f51])).

fof(f51,plain,(
    k1_zfmisc_1(sK1) = k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f37,f28,f45,f28])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f74,plain,(
    ! [X0] : r2_hidden(k3_tarski(sK1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f43,f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f66,f68])).

fof(f68,plain,(
    ! [X0] : k5_setfam_1(X0,sK1) = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK1,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f38,f28])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k5_setfam_1(X0,sK1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,(
    ~ v1_xboole_0(k3_tarski(sK1)) ),
    inference(backward_demodulation,[],[f58,f81])).

fof(f81,plain,(
    u1_struct_0(sK0) = k3_tarski(sK1) ),
    inference(forward_demodulation,[],[f77,f68])).

fof(f77,plain,(
    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f27,f52,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f27,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f30,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f30,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (5097)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.50  % (5108)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.50  % (5108)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (5091)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.52  % (5089)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f120,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(subsumption_resolution,[],[f113,f53])).
% 1.19/0.52  fof(f53,plain,(
% 1.19/0.52    v1_xboole_0(sK1)),
% 1.19/0.52    inference(definition_unfolding,[],[f39,f28])).
% 1.19/0.52  fof(f28,plain,(
% 1.19/0.52    k1_xboole_0 = sK1),
% 1.19/0.52    inference(cnf_transformation,[],[f16])).
% 1.19/0.52  fof(f16,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.19/0.52    inference(flattening,[],[f15])).
% 1.19/0.52  fof(f15,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f14])).
% 1.19/0.52  fof(f14,negated_conjecture,(
% 1.19/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.19/0.52    inference(negated_conjecture,[],[f13])).
% 1.19/0.52  fof(f13,conjecture,(
% 1.19/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 1.19/0.52  fof(f39,plain,(
% 1.19/0.52    v1_xboole_0(k1_xboole_0)),
% 1.19/0.52    inference(cnf_transformation,[],[f1])).
% 1.19/0.52  fof(f1,axiom,(
% 1.19/0.52    v1_xboole_0(k1_xboole_0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.19/0.52  fof(f113,plain,(
% 1.19/0.52    ~v1_xboole_0(sK1)),
% 1.19/0.52    inference(backward_demodulation,[],[f83,f101])).
% 1.19/0.52  fof(f101,plain,(
% 1.19/0.52    sK1 = k3_tarski(sK1)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f74,f64])).
% 1.19/0.52  fof(f64,plain,(
% 1.19/0.52    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK1)) | sK1 = X0) )),
% 1.19/0.52    inference(superposition,[],[f54,f51])).
% 1.19/0.52  fof(f51,plain,(
% 1.19/0.52    k1_zfmisc_1(sK1) = k2_tarski(sK1,sK1)),
% 1.19/0.52    inference(definition_unfolding,[],[f37,f28,f45,f28])).
% 1.19/0.52  fof(f45,plain,(
% 1.19/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f3])).
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.52  fof(f37,plain,(
% 1.19/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.19/0.52    inference(cnf_transformation,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.19/0.52  fof(f54,plain,(
% 1.19/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 1.19/0.52    inference(equality_resolution,[],[f49])).
% 1.19/0.52  fof(f49,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 1.19/0.52    inference(definition_unfolding,[],[f32,f45])).
% 1.19/0.52  fof(f32,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.19/0.52    inference(cnf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.19/0.52  fof(f74,plain,(
% 1.19/0.52    ( ! [X0] : (r2_hidden(k3_tarski(sK1),k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f43,f71,f42])).
% 1.19/0.52  fof(f42,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.19/0.52    inference(flattening,[],[f21])).
% 1.19/0.52  fof(f21,plain,(
% 1.19/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f9])).
% 1.19/0.52  fof(f9,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.19/0.52  fof(f71,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(backward_demodulation,[],[f66,f68])).
% 1.19/0.52  fof(f68,plain,(
% 1.19/0.52    ( ! [X0] : (k5_setfam_1(X0,sK1) = k3_tarski(sK1)) )),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f52,f46])).
% 1.19/0.52  fof(f46,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f25])).
% 1.19/0.52  fof(f25,plain,(
% 1.19/0.52    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.52    inference(ennf_transformation,[],[f8])).
% 1.19/0.52  fof(f8,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 1.19/0.52  fof(f52,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(definition_unfolding,[],[f38,f28])).
% 1.19/0.52  fof(f38,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.19/0.52  fof(f66,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(k5_setfam_1(X0,sK1),k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f52,f41])).
% 1.19/0.52  fof(f41,plain,(
% 1.19/0.52    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f20])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.52    inference(ennf_transformation,[],[f7])).
% 1.19/0.52  fof(f7,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.19/0.52  fof(f43,plain,(
% 1.19/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f5])).
% 1.19/0.52  fof(f5,axiom,(
% 1.19/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.19/0.52  fof(f83,plain,(
% 1.19/0.52    ~v1_xboole_0(k3_tarski(sK1))),
% 1.19/0.52    inference(backward_demodulation,[],[f58,f81])).
% 1.19/0.52  fof(f81,plain,(
% 1.19/0.52    u1_struct_0(sK0) = k3_tarski(sK1)),
% 1.19/0.52    inference(forward_demodulation,[],[f77,f68])).
% 1.19/0.52  fof(f77,plain,(
% 1.19/0.52    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),sK1)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f27,f52,f36])).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f17])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.52    inference(ennf_transformation,[],[f11])).
% 1.19/0.52  fof(f11,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 1.19/0.52    inference(cnf_transformation,[],[f16])).
% 1.19/0.52  fof(f58,plain,(
% 1.19/0.52    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f29,f30,f44])).
% 1.19/0.52  fof(f44,plain,(
% 1.19/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f24])).
% 1.19/0.52  fof(f24,plain,(
% 1.19/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.19/0.52    inference(flattening,[],[f23])).
% 1.19/0.52  fof(f23,plain,(
% 1.19/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f12])).
% 1.19/0.52  fof(f12,axiom,(
% 1.19/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.19/0.52  fof(f30,plain,(
% 1.19/0.52    l1_struct_0(sK0)),
% 1.19/0.52    inference(cnf_transformation,[],[f16])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    ~v2_struct_0(sK0)),
% 1.19/0.52    inference(cnf_transformation,[],[f16])).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (5108)------------------------------
% 1.19/0.52  % (5108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (5108)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (5108)Memory used [KB]: 1791
% 1.19/0.52  % (5108)Time elapsed: 0.084 s
% 1.19/0.52  % (5108)------------------------------
% 1.19/0.52  % (5108)------------------------------
% 1.19/0.53  % (5088)Success in time 0.156 s
%------------------------------------------------------------------------------
