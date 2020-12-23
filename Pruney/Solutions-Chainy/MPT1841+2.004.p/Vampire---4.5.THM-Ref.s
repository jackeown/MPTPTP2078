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
% DateTime   : Thu Dec  3 13:20:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 258 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f80,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK1)) ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tarski(sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f69,plain,(
    v1_xboole_0(k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f67,f52])).

fof(f52,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f22,f51])).

fof(f51,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f24,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f49,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f22,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f55,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f28,f51])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f44,f23])).

fof(f23,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (22229)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.46  % (22229)Refutation not found, incomplete strategy% (22229)------------------------------
% 0.21/0.46  % (22229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (22229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (22229)Memory used [KB]: 10618
% 0.21/0.46  % (22229)Time elapsed: 0.045 s
% 0.21/0.46  % (22229)------------------------------
% 0.21/0.46  % (22229)------------------------------
% 0.21/0.46  % (22237)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.46  % (22237)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(resolution,[],[f80,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.21/0.46    inference(equality_resolution,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.21/0.46    inference(equality_resolution,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK1))) )),
% 0.21/0.46    inference(resolution,[],[f78,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(sK1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f71,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_tarski(sK1))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.46    inference(resolution,[],[f69,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    v1_xboole_0(k1_tarski(sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f67,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    v1_subset_1(k1_tarski(sK1),sK0)),
% 0.21/0.46    inference(backward_demodulation,[],[f22,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.21/0.47    inference(resolution,[],[f27,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    v1_xboole_0(k1_tarski(sK1)) | ~v1_subset_1(k1_tarski(sK1),sK0)),
% 0.21/0.47    inference(resolution,[],[f65,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f24])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f21])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(superposition,[],[f28,f51])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | ~v1_subset_1(X0,sK0)) )),
% 0.21/0.47    inference(resolution,[],[f44,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v1_zfmisc_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f26,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22237)------------------------------
% 0.21/0.47  % (22237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22237)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22237)Memory used [KB]: 1663
% 0.21/0.47  % (22237)Time elapsed: 0.057 s
% 0.21/0.47  % (22237)------------------------------
% 0.21/0.47  % (22237)------------------------------
% 0.21/0.47  % (22217)Success in time 0.113 s
%------------------------------------------------------------------------------
