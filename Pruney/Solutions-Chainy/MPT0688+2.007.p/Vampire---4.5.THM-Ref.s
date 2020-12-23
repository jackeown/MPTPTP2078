%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  31 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  92 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(global_subsumption,[],[f11,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f30,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f30,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,k2_relat_1(sK1)),sK0)
      | r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f29,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(global_subsumption,[],[f10,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f9,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f9,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (7957)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (7956)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (7964)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (7964)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f11,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1)) | r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f30,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,k2_relat_1(sK1)),sK0) | r1_tarski(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(resolution,[],[f29,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f10,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(superposition,[],[f9,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~v1_relat_1(X1) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f5])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f3])).
% 0.21/0.52  fof(f3,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7964)------------------------------
% 0.21/0.52  % (7964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7964)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7964)Memory used [KB]: 10618
% 0.21/0.52  % (7964)Time elapsed: 0.051 s
% 0.21/0.52  % (7964)------------------------------
% 0.21/0.52  % (7964)------------------------------
% 0.21/0.52  % (7950)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (7948)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (7940)Success in time 0.155 s
%------------------------------------------------------------------------------
