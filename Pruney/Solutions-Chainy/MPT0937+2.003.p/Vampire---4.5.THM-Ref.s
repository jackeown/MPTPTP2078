%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 149 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(resolution,[],[f65,f14])).

fof(f14,plain,(
    ~ v1_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ v1_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(f65,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_relat_2(k1_wellord2(X0),X0)
      | v1_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f41,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | v1_relat_2(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f16,f38])).

fof(f38,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f31,f15])).

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
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(f64,plain,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( r1_relat_2(k1_wellord2(X0),X0)
      | r1_relat_2(k1_wellord2(X0),X0) ) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X1)
      | r1_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK1(X0,X1),X1)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f60,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK1(k1_wellord2(X5),X6),X5)
      | r1_relat_2(k1_wellord2(X5),X6) ) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f58,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK1(k1_wellord2(X5),X6),X5)
      | ~ v1_relat_1(k1_wellord2(X5))
      | r1_relat_2(k1_wellord2(X5),X6) ) ),
    inference(resolution,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f40,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f37,f15])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (23091)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (23083)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (23083)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f65,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ~v1_relat_2(k1_wellord2(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : ~v1_relat_2(k1_wellord2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_2(k1_wellord2(X0))) )),
% 0.21/0.52    inference(resolution,[],[f64,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_relat_2(k1_wellord2(X0),X0) | v1_relat_2(k1_wellord2(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f41,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_relat_2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0)) | v1_relat_2(k1_wellord2(X0))) )),
% 0.21/0.52    inference(superposition,[],[f16,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f15])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0) | v1_relat_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0) | r1_relat_2(k1_wellord2(X0),X0)) )),
% 0.21/0.52    inference(resolution,[],[f60,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X1) | r1_relat_2(k1_wellord2(X0),X1)) )),
% 0.21/0.52    inference(resolution,[],[f19,f15])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK1(X0,X1),X1) | r1_relat_2(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X6,X5] : (~r2_hidden(sK1(k1_wellord2(X5),X6),X5) | r1_relat_2(k1_wellord2(X5),X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f15])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X6,X5] : (~r2_hidden(sK1(k1_wellord2(X5),X6),X5) | ~v1_relat_1(k1_wellord2(X5)) | r1_relat_2(k1_wellord2(X5),X6)) )),
% 0.21/0.52    inference(resolution,[],[f55,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0) | ~v1_relat_1(X0) | r1_relat_2(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))) )),
% 0.21/0.52    inference(resolution,[],[f40,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f37,f15])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23083)------------------------------
% 0.21/0.52  % (23083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23083)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23083)Memory used [KB]: 6268
% 0.21/0.52  % (23083)Time elapsed: 0.098 s
% 0.21/0.52  % (23083)------------------------------
% 0.21/0.52  % (23083)------------------------------
% 0.21/0.52  % (23076)Success in time 0.154 s
%------------------------------------------------------------------------------
