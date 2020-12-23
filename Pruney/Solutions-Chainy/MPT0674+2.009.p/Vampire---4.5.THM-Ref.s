%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 105 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   15
%              Number of atoms          :  111 ( 348 expanded)
%              Number of equality atoms :   36 (  94 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f14])).

fof(f14,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f85,plain,(
    k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f82,f13])).

fof(f13,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k11_relat_1(sK1,X0) = k1_tarski(k1_funct_1(sK1,X0)) ) ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK1,X2),k11_relat_1(sK1,X2))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f20,f11])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f42,f11])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(resolution,[],[f27,f12])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k11_relat_1(sK1,X3))
      | k1_tarski(X2) = k11_relat_1(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f80,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X0
      | ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = X1 ) ),
    inference(inner_rewriting,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f80,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k11_relat_1(sK1,X3))
      | k1_tarski(X2) = k11_relat_1(sK1,X3)
      | sK2(X2,k11_relat_1(sK1,X3)) = X2 ) ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f19,f11])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f38,f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f22,f12])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X3) != X2
      | ~ r2_hidden(X2,k11_relat_1(sK1,X3))
      | k1_tarski(X2) = k11_relat_1(sK1,X3)
      | sK2(X2,k11_relat_1(sK1,X3)) = X2 ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X3) != X2
      | ~ r2_hidden(X2,k11_relat_1(sK1,X3))
      | k1_tarski(X2) = k11_relat_1(sK1,X3)
      | sK2(X2,k11_relat_1(sK1,X3)) = X2
      | k1_tarski(X2) = k11_relat_1(sK1,X3) ) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK2(X1,k11_relat_1(sK1,X0)) = k1_funct_1(sK1,X0)
      | sK2(X1,k11_relat_1(sK1,X0)) = X1
      | k1_tarski(X1) = k11_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f40,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | sK2(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18135)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18135)Refutation not found, incomplete strategy% (18135)------------------------------
% 0.21/0.50  % (18135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18135)Memory used [KB]: 6012
% 0.21/0.50  % (18135)Time elapsed: 0.085 s
% 0.21/0.50  % (18135)------------------------------
% 0.21/0.50  % (18135)------------------------------
% 0.21/0.50  % (18141)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (18153)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (18131)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (18153)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.50    inference(resolution,[],[f82,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k11_relat_1(sK1,X0) = k1_tarski(k1_funct_1(sK1,X0))) )),
% 0.21/0.50    inference(resolution,[],[f81,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(k1_funct_1(sK1,X2),k11_relat_1(sK1,X2)) | ~r2_hidden(X2,k1_relat_1(sK1))) )),
% 0.21/0.50    inference(resolution,[],[f43,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK1) | r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.21/0.50    inference(resolution,[],[f20,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f11])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 0.21/0.50    inference(resolution,[],[f27,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(X2,k11_relat_1(sK1,X3)) | k1_tarski(X2) = k11_relat_1(sK1,X3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK2(X0,X1) != X0 | ~r2_hidden(X0,X1) | k1_tarski(X0) = X1) )),
% 0.21/0.50    inference(inner_rewriting,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(X2,k11_relat_1(sK1,X3)) | k1_tarski(X2) = k11_relat_1(sK1,X3) | sK2(X2,k11_relat_1(sK1,X3)) = X2) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) )),
% 0.21/0.50    inference(resolution,[],[f39,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.21/0.50    inference(resolution,[],[f19,f11])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f38,f11])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.21/0.50    inference(resolution,[],[f22,f12])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_funct_1(sK1,X3) != X2 | ~r2_hidden(X2,k11_relat_1(sK1,X3)) | k1_tarski(X2) = k11_relat_1(sK1,X3) | sK2(X2,k11_relat_1(sK1,X3)) = X2) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_funct_1(sK1,X3) != X2 | ~r2_hidden(X2,k11_relat_1(sK1,X3)) | k1_tarski(X2) = k11_relat_1(sK1,X3) | sK2(X2,k11_relat_1(sK1,X3)) = X2 | k1_tarski(X2) = k11_relat_1(sK1,X3)) )),
% 0.21/0.50    inference(superposition,[],[f28,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK2(X1,k11_relat_1(sK1,X0)) = k1_funct_1(sK1,X0) | sK2(X1,k11_relat_1(sK1,X0)) = X1 | k1_tarski(X1) = k11_relat_1(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f40,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (18153)------------------------------
% 0.21/0.50  % (18153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18153)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (18153)Memory used [KB]: 10618
% 0.21/0.50  % (18153)Time elapsed: 0.069 s
% 0.21/0.50  % (18153)------------------------------
% 0.21/0.50  % (18153)------------------------------
% 0.21/0.50  % (18131)Refutation not found, incomplete strategy% (18131)------------------------------
% 0.21/0.50  % (18131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18131)Memory used [KB]: 10490
% 0.21/0.50  % (18131)Time elapsed: 0.094 s
% 0.21/0.50  % (18131)------------------------------
% 0.21/0.50  % (18131)------------------------------
% 0.21/0.50  % (18129)Success in time 0.148 s
%------------------------------------------------------------------------------
