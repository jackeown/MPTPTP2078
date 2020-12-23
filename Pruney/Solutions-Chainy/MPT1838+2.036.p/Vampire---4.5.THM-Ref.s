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
% DateTime   : Thu Dec  3 13:19:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 200 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  134 ( 502 expanded)
%              Number of equality atoms :   70 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f33,f41,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f100,plain,(
    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0)) ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f89,plain,(
    r1_tarski(k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f59,f81])).

fof(f81,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f79,f69])).

fof(f69,plain,(
    sK1 = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) ),
    inference(forward_demodulation,[],[f68,f63])).

fof(f63,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f22,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f52,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f21,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f67,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f66,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f50,f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_enumset1(X0,X0,X0) = k6_domain_1(sK1,X0) ) ),
    inference(resolution,[],[f21,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f79,plain,(
    ! [X0] :
      ( sK1 != k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f62,f76])).

fof(f76,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f74,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f74,plain,(
    ! [X3] : k1_xboole_0 != k3_tarski(k1_enumset1(sK1,sK1,X3)) ),
    inference(superposition,[],[f44,f69])).

fof(f62,plain,(
    ! [X0] :
      ( sK1 != k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0] :
      ( sK1 != k1_enumset1(X0,X0,X0)
      | sK0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f49,f56])).

fof(f56,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f23,f45])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2))
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f40,f42,f41])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f59,plain,(
    r1_tarski(k1_enumset1(sK3(sK0),sK3(sK0),sK3(sK0)),sK0) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f54,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f25,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (23397)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (23389)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (23380)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (23382)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (23397)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f100,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f33,f41,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f34,f35])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0))),
% 0.22/0.52    inference(resolution,[],[f89,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 0.22/0.52    inference(definition_unfolding,[],[f36,f41])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    r1_tarski(k1_enumset1(sK3(k1_xboole_0),sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f59,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    k1_xboole_0 = sK0),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sK1 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.52    inference(superposition,[],[f79,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    sK1 = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f68,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f52,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f21,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ~v1_xboole_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f67,f22])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) | ~v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f66,f21])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    k6_domain_1(sK1,sK2(sK1)) = k1_enumset1(sK2(sK1),sK2(sK1),sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f50,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_enumset1(X0,X0,X0) = k6_domain_1(sK1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f21,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f37,f42])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | k1_xboole_0 = sK0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f62,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(superposition,[],[f74,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f26,f41])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X3] : (k1_xboole_0 != k3_tarski(k1_enumset1(sK1,sK1,X3))) )),
% 0.22/0.52    inference(superposition,[],[f44,f69])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 != k1_enumset1(X0,X0,X0) | sK0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(superposition,[],[f49,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f23,f45])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2)) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f42,f41])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    r1_tarski(k1_enumset1(sK3(sK0),sK3(sK0),sK3(sK0)),sK0)),
% 0.22/0.52    inference(resolution,[],[f54,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f38,f42])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0),sK0)),
% 0.22/0.52    inference(resolution,[],[f25,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ~v1_xboole_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23397)------------------------------
% 0.22/0.52  % (23397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23397)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23397)Memory used [KB]: 1791
% 0.22/0.52  % (23397)Time elapsed: 0.061 s
% 0.22/0.52  % (23397)------------------------------
% 0.22/0.52  % (23397)------------------------------
% 0.22/0.52  % (23375)Success in time 0.165 s
%------------------------------------------------------------------------------
