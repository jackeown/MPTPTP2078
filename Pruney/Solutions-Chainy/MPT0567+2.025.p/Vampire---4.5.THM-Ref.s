%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  43 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 103 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f58,plain,(
    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f50,f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f50,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))
      | ~ r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) ) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3,sK0),X3)
      | ~ r2_hidden(X2,k10_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f14,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X1,X0,sK0),k1_xboole_0)
      | ~ r2_hidden(X1,k10_relat_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f41,f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X1,X0,sK0),k1_xboole_0)
      | ~ r2_hidden(sK3(X1,X0,sK0),X0)
      | ~ r2_hidden(X1,k10_relat_1(sK0,X0)) ) ),
    inference(superposition,[],[f33,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,k5_xboole_0(X1,X2),sK0),X2)
      | ~ r2_hidden(sK3(X0,k5_xboole_0(X1,X2),sK0),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK0,k5_xboole_0(X1,X2))) ) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (7991)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.49  % (7983)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (7991)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f58,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f50,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0)) | ~r2_hidden(X0,k10_relat_1(sK0,k1_xboole_0))) )),
% 0.22/0.50    inference(resolution,[],[f44,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,sK0),X3) | ~r2_hidden(X2,k10_relat_1(sK0,X3))) )),
% 0.22/0.50    inference(resolution,[],[f14,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(sK3(X1,X0,sK0),k1_xboole_0) | ~r2_hidden(X1,k10_relat_1(sK0,X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f41,f31])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(sK3(X1,X0,sK0),k1_xboole_0) | ~r2_hidden(sK3(X1,X0,sK0),X0) | ~r2_hidden(X1,k10_relat_1(sK0,X0))) )),
% 0.22/0.50    inference(superposition,[],[f33,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,k5_xboole_0(X1,X2),sK0),X2) | ~r2_hidden(sK3(X0,k5_xboole_0(X1,X2),sK0),X1) | ~r2_hidden(X0,k10_relat_1(sK0,k5_xboole_0(X1,X2)))) )),
% 0.22/0.50    inference(resolution,[],[f31,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (7991)------------------------------
% 0.22/0.50  % (7991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7991)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (7991)Memory used [KB]: 1663
% 0.22/0.50  % (7991)Time elapsed: 0.008 s
% 0.22/0.50  % (7991)------------------------------
% 0.22/0.50  % (7991)------------------------------
% 0.22/0.50  % (7969)Success in time 0.134 s
%------------------------------------------------------------------------------
