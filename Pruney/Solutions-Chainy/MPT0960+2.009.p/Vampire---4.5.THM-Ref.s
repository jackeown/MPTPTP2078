%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  56 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 121 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f86,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(superposition,[],[f69,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(forward_demodulation,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f31,f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f44,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f18,f17])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f69,plain,(
    ! [X0,X1] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1),X0))) ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1),X0))) ) ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(X0),X2),X1))) ) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f63,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k1_wellord2(X1)),X1) ),
    inference(superposition,[],[f41,f45])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f16,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (7305)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (7305)Refutation not found, incomplete strategy% (7305)------------------------------
% 0.21/0.44  % (7305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (7305)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (7305)Memory used [KB]: 10490
% 0.21/0.44  % (7305)Time elapsed: 0.056 s
% 0.21/0.44  % (7305)------------------------------
% 0.21/0.44  % (7305)------------------------------
% 0.21/0.45  % (7322)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (7321)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (7323)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.46  % (7321)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f16,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.21/0.46    inference(resolution,[],[f86,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.46    inference(superposition,[],[f69,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0) )),
% 0.21/0.46    inference(forward_demodulation,[],[f44,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f31,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.46    inference(equality_resolution,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) )),
% 0.21/0.46    inference(resolution,[],[f18,f17])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1),X0)))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f67,f17])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1),X0)))) )),
% 0.21/0.46    inference(resolution,[],[f63,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(X0),X2),X1)))) )),
% 0.21/0.46    inference(resolution,[],[f30,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X1] : (r1_tarski(k2_relat_1(k1_wellord2(X1)),X1)) )),
% 0.21/0.46    inference(superposition,[],[f41,f45])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(superposition,[],[f19,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7321)------------------------------
% 0.21/0.46  % (7321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7321)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7321)Memory used [KB]: 1663
% 0.21/0.46  % (7321)Time elapsed: 0.077 s
% 0.21/0.46  % (7321)------------------------------
% 0.21/0.46  % (7321)------------------------------
% 0.21/0.46  % (7295)Success in time 0.107 s
%------------------------------------------------------------------------------
