%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 118 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 259 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(resolution,[],[f108,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f108,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f104,f74])).

fof(f74,plain,(
    sK0 = k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) = sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f59,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sK7(X0,X1,X3) = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f59,plain,(
    r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f9,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f9,plain,(
    ~ r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_2)).

fof(f65,plain,(
    sK0 = k1_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f59,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | k1_relat_1(sK7(X0,X1,X3)) = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK7(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ~ r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f76,f77,f75,f60,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(k1_relat_1(X4),X0)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,k4_partfun1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(k1_relat_1(X4),X0)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X4,X2)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | X3 != X4
      | ~ r1_tarski(k1_relat_1(X4),X0)
      | ~ r1_tarski(k2_relat_1(X4),X1)
      | r2_hidden(X3,X2)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_partfun1)).

fof(f60,plain,(
    ~ r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k4_partfun1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f9,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1) ),
    inference(backward_demodulation,[],[f66,f64])).

fof(f66,plain,(
    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f77,plain,(
    v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f62,f64])).

fof(f62,plain,(
    v1_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f59,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v1_relat_1(sK7(X0,X1,X3))
      | ~ r2_hidden(X3,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK7(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f63,f64])).

fof(f63,plain,(
    v1_funct_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_funct_1(sK7(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK7(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (3255)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.49  % (3269)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.49  % (3263)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (3257)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (3256)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (3256)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f108,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f104,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),
% 0.22/0.51    inference(backward_demodulation,[],[f65,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)) = sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f59,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sK7(X0,X1,X3) = X3) )),
% 0.22/0.51    inference(equality_resolution,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (sK7(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k1_funct_2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f9,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ~r1_tarski(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1] : ~r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_2)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f59,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | k1_relat_1(sK7(X0,X1,X3)) = X0) )),
% 0.22/0.51    inference(equality_resolution,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK7(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f76,f77,f75,f60,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r1_tarski(k1_relat_1(X4),X0) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,k4_partfun1(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r1_tarski(k1_relat_1(X4),X0) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X4,X2) | k4_partfun1(X0,X1) != X2) )),
% 0.22/0.51    inference(equality_resolution,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | ~v1_funct_1(X4) | X3 != X4 | ~r1_tarski(k1_relat_1(X4),X0) | ~r1_tarski(k2_relat_1(X4),X1) | r2_hidden(X3,X2) | k4_partfun1(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_partfun1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & r1_tarski(k1_relat_1(X4),X0) & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_partfun1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~r2_hidden(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)),k4_partfun1(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f9,f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))),sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f66,f64])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),sK1)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f59,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    v1_relat_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),
% 0.22/0.51    inference(forward_demodulation,[],[f62,f64])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    v1_relat_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f59,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (v1_relat_1(sK7(X0,X1,X3)) | ~r2_hidden(X3,k1_funct_2(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK7(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    v1_funct_1(sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1)))),
% 0.22/0.51    inference(forward_demodulation,[],[f63,f64])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    v1_funct_1(sK7(sK0,sK1,sK2(k1_funct_2(sK0,sK1),k4_partfun1(sK0,sK1))))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f59,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_funct_1(sK7(X0,X1,X3))) )),
% 0.22/0.51    inference(equality_resolution,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK7(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (3256)------------------------------
% 0.22/0.51  % (3256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3256)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (3256)Memory used [KB]: 6268
% 0.22/0.51  % (3256)Time elapsed: 0.106 s
% 0.22/0.51  % (3256)------------------------------
% 0.22/0.51  % (3256)------------------------------
% 0.22/0.51  % (3251)Success in time 0.152 s
%------------------------------------------------------------------------------
