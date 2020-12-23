%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  66 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 351 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f14,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

fof(f54,plain,(
    ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK2),X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f20,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f48,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f47,f25])).

fof(f25,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f24,f16])).

fof(f16,plain,(
    v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v5_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f12,f13])).

fof(f12,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f19,f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X6] :
      ( r1_tarski(X6,sK1)
      | ~ r1_tarski(X6,sK0) ) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.40  % (27417)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.40  % (27417)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f55,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(subsumption_resolution,[],[f54,f14])).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    v5_relat_1(sK2,sK0)),
% 0.21/0.40    inference(cnf_transformation,[],[f8])).
% 0.21/0.40  fof(f8,plain,(
% 0.21/0.40    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(X2) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) & v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.21/0.40    inference(flattening,[],[f7])).
% 0.21/0.40  fof(f7,plain,(
% 0.21/0.40    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(X2) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) & (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.21/0.40    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v1_relat_1(X2))))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v1_relat_1(X2))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ~v5_relat_1(sK2,sK0)),
% 0.21/0.41    inference(resolution,[],[f48,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),X0) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.41    inference(resolution,[],[f20,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    ~r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.41    inference(subsumption_resolution,[],[f47,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ~v5_relat_1(sK2,sK1)),
% 0.21/0.41    inference(subsumption_resolution,[],[f24,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    v5_ordinal1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ~v5_relat_1(sK2,sK1) | ~v5_ordinal1(sK2)),
% 0.21/0.41    inference(subsumption_resolution,[],[f23,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    v1_funct_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v5_ordinal1(sK2)),
% 0.21/0.41    inference(subsumption_resolution,[],[f12,f13])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v5_ordinal1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    ~r1_tarski(k2_relat_1(sK2),sK0) | v5_relat_1(sK2,sK1)),
% 0.21/0.41    inference(resolution,[],[f40,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v5_relat_1(sK2,X0)) )),
% 0.21/0.41    inference(resolution,[],[f19,f13])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X6] : (r1_tarski(X6,sK1) | ~r1_tarski(X6,sK0)) )),
% 0.21/0.41    inference(superposition,[],[f28,f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.41    inference(resolution,[],[f21,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.21/0.41    inference(superposition,[],[f22,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (27417)------------------------------
% 0.21/0.41  % (27417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (27417)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (27417)Memory used [KB]: 10618
% 0.21/0.41  % (27417)Time elapsed: 0.004 s
% 0.21/0.41  % (27417)------------------------------
% 0.21/0.41  % (27417)------------------------------
% 0.21/0.41  % (27406)Success in time 0.051 s
%------------------------------------------------------------------------------
