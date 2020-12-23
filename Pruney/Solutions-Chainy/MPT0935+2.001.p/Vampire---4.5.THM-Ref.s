%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  27 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  51 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f16,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | k1_relat_1(X4) = k2_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(f19,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK3,sK4))) ),
    inference(backward_demodulation,[],[f14,f18])).

fof(f14,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(definition_unfolding,[],[f9,f10,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f9,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.55  % (5788)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (5788)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f19,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f16,f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.56    inference(equality_resolution,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | k1_relat_1(X4) = k2_tarski(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 0.22/0.56    inference(flattening,[],[f7])).
% 0.22/0.56  fof(f7,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    k2_tarski(sK0,sK3) != k1_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK3,sK4)))),
% 0.22/0.56    inference(backward_demodulation,[],[f14,f18])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5))))),
% 0.22/0.56    inference(definition_unfolding,[],[f9,f10,f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3)),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)),
% 0.22/0.56    inference(negated_conjecture,[],[f4])).
% 0.22/0.56  fof(f4,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (5788)------------------------------
% 0.22/0.56  % (5788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5788)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (5788)Memory used [KB]: 6140
% 0.22/0.56  % (5788)Time elapsed: 0.005 s
% 0.22/0.56  % (5788)------------------------------
% 0.22/0.56  % (5788)------------------------------
% 0.22/0.57  % (5781)Success in time 0.196 s
%------------------------------------------------------------------------------
