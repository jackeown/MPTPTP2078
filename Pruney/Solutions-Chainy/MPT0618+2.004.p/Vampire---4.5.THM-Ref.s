%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  74 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   15
%              Number of atoms          :   83 ( 233 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f14])).

fof(f14,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f88,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f87,f25])).

fof(f25,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ~ r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f86,f12])).

fof(f86,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f83,f15])).

fof(f15,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(superposition,[],[f17,f81])).

fof(f81,plain,(
    k1_funct_1(sK1,sK0) = sK2(sK0,k2_relat_1(sK1),sK1) ),
    inference(resolution,[],[f75,f14])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = sK2(X0,k2_relat_1(sK1),sK1) ) ),
    inference(superposition,[],[f58,f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | sK2(X0,X1,sK1) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f56,f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1,sK1) = k1_funct_1(sK1,X0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

% (14717)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f37,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f34,f12])).

fof(f34,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(resolution,[],[f13,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:21:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (14722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (14704)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (14715)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (14722)Refutation not found, incomplete strategy% (14722)------------------------------
% 0.22/0.49  % (14722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14722)Memory used [KB]: 10490
% 0.22/0.49  % (14722)Time elapsed: 0.071 s
% 0.22/0.49  % (14722)------------------------------
% 0.22/0.49  % (14722)------------------------------
% 0.22/0.49  % (14715)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1] : (~r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1] : ((~r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f87,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f12,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f86,f12])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.22/0.49    inference(superposition,[],[f17,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK0) = sK2(sK0,k2_relat_1(sK1),sK1)),
% 0.22/0.49    inference(resolution,[],[f75,f14])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = sK2(X0,k2_relat_1(sK1),sK1)) )),
% 0.22/0.49    inference(superposition,[],[f58,f25])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | sK2(X0,X1,sK1) = k1_funct_1(sK1,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f56,f12])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sK2(X0,X1,sK1) = k1_funct_1(sK1,X0) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.49    inference(resolution,[],[f37,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  % (14717)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f34,f12])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 0.22/0.49    inference(resolution,[],[f13,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (14715)------------------------------
% 0.22/0.49  % (14715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14715)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (14715)Memory used [KB]: 1663
% 0.22/0.49  % (14715)Time elapsed: 0.073 s
% 0.22/0.49  % (14715)------------------------------
% 0.22/0.49  % (14715)------------------------------
% 0.22/0.50  % (14701)Success in time 0.13 s
%------------------------------------------------------------------------------
