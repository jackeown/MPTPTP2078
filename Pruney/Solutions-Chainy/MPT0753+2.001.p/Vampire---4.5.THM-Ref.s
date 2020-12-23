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
% DateTime   : Thu Dec  3 12:55:45 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 178 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f25])).

fof(f25,plain,(
    ~ v5_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f23,f24])).

fof(f24,plain,(
    v5_ordinal1(sK0) ),
    inference(resolution,[],[f13,f12])).

fof(f12,plain,(
    v3_ordinal1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_relat_1(X0))
      | v5_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f23,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v5_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f22,f11])).

fof(f11,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f9,f10])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    v5_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
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

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | v5_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f15,f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.26  % Computer   : n002.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 11:08:21 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.11/0.36  % (7527)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.11/0.36  % (7527)Refutation not found, incomplete strategy% (7527)------------------------------
% 0.11/0.36  % (7527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (7518)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.11/0.37  % (7527)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.37  
% 0.11/0.37  % (7527)Memory used [KB]: 6140
% 0.11/0.37  % (7527)Time elapsed: 0.064 s
% 0.11/0.37  % (7527)------------------------------
% 0.11/0.37  % (7527)------------------------------
% 0.11/0.37  % (7518)Refutation not found, incomplete strategy% (7518)------------------------------
% 0.11/0.37  % (7518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (7518)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.37  
% 0.11/0.37  % (7518)Memory used [KB]: 6012
% 0.11/0.37  % (7518)Time elapsed: 0.071 s
% 0.11/0.37  % (7518)------------------------------
% 0.11/0.37  % (7518)------------------------------
% 0.11/0.38  % (7533)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.11/0.38  % (7533)Refutation found. Thanks to Tanya!
% 0.11/0.38  % SZS status Theorem for theBenchmark
% 0.11/0.38  % SZS output start Proof for theBenchmark
% 0.11/0.38  fof(f29,plain,(
% 0.11/0.38    $false),
% 0.11/0.38    inference(subsumption_resolution,[],[f28,f25])).
% 0.11/0.38  fof(f25,plain,(
% 0.11/0.38    ~v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.11/0.38    inference(subsumption_resolution,[],[f23,f24])).
% 0.11/0.38  fof(f24,plain,(
% 0.11/0.38    v5_ordinal1(sK0)),
% 0.11/0.38    inference(resolution,[],[f13,f12])).
% 0.11/0.38  fof(f12,plain,(
% 0.11/0.38    v3_ordinal1(k1_relat_1(sK0))),
% 0.11/0.38    inference(cnf_transformation,[],[f7])).
% 0.11/0.38  fof(f7,plain,(
% 0.11/0.38    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.11/0.38    inference(flattening,[],[f6])).
% 0.11/0.38  fof(f6,plain,(
% 0.11/0.38    ? [X0] : (((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.11/0.38    inference(ennf_transformation,[],[f5])).
% 0.11/0.38  fof(f5,negated_conjecture,(
% 0.11/0.38    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.11/0.38    inference(negated_conjecture,[],[f4])).
% 0.11/0.38  fof(f4,conjecture,(
% 0.11/0.38    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.11/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).
% 0.11/0.38  fof(f13,plain,(
% 0.11/0.38    ( ! [X0] : (~v3_ordinal1(k1_relat_1(X0)) | v5_ordinal1(X0)) )),
% 0.11/0.38    inference(cnf_transformation,[],[f3])).
% 0.11/0.38  fof(f3,axiom,(
% 0.11/0.38    ! [X0] : (v5_ordinal1(X0) <=> v3_ordinal1(k1_relat_1(X0)))),
% 0.11/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).
% 0.11/0.38  fof(f23,plain,(
% 0.11/0.38    ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v5_ordinal1(sK0)),
% 0.11/0.38    inference(subsumption_resolution,[],[f22,f11])).
% 0.11/0.38  fof(f11,plain,(
% 0.11/0.38    v1_funct_1(sK0)),
% 0.11/0.38    inference(cnf_transformation,[],[f7])).
% 0.11/0.38  fof(f22,plain,(
% 0.11/0.38    ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0)),
% 0.11/0.38    inference(subsumption_resolution,[],[f9,f10])).
% 0.11/0.38  fof(f10,plain,(
% 0.11/0.38    v1_relat_1(sK0)),
% 0.11/0.38    inference(cnf_transformation,[],[f7])).
% 0.11/0.38  fof(f9,plain,(
% 0.11/0.38    ~v1_relat_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0)),
% 0.11/0.38    inference(cnf_transformation,[],[f7])).
% 0.11/0.38  fof(f28,plain,(
% 0.11/0.38    v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.11/0.38    inference(resolution,[],[f27,f20])).
% 0.11/0.38  fof(f20,plain,(
% 0.11/0.38    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.11/0.38    inference(equality_resolution,[],[f18])).
% 0.11/0.38  fof(f18,plain,(
% 0.11/0.38    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.11/0.38    inference(cnf_transformation,[],[f1])).
% 0.11/0.38  fof(f1,axiom,(
% 0.11/0.38    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.11/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.11/0.38  fof(f27,plain,(
% 0.11/0.38    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | v5_relat_1(sK0,X0)) )),
% 0.11/0.38    inference(resolution,[],[f15,f10])).
% 0.11/0.38  fof(f15,plain,(
% 0.11/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.11/0.38    inference(cnf_transformation,[],[f8])).
% 0.11/0.38  fof(f8,plain,(
% 0.11/0.38    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.11/0.38    inference(ennf_transformation,[],[f2])).
% 0.11/0.38  fof(f2,axiom,(
% 0.11/0.38    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.11/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.11/0.38  % SZS output end Proof for theBenchmark
% 0.11/0.38  % (7533)------------------------------
% 0.11/0.38  % (7533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.38  % (7533)Termination reason: Refutation
% 0.11/0.38  
% 0.11/0.38  % (7533)Memory used [KB]: 1535
% 0.11/0.38  % (7533)Time elapsed: 0.070 s
% 0.11/0.38  % (7533)------------------------------
% 0.11/0.38  % (7533)------------------------------
% 0.11/0.38  % (7510)Success in time 0.108 s
%------------------------------------------------------------------------------
