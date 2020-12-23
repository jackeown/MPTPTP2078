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
% DateTime   : Thu Dec  3 12:50:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 173 expanded)
%              Number of leaves         :    4 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  120 ( 493 expanded)
%              Number of equality atoms :   28 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f11])).

fof(f11,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f300,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f299,f184])).

fof(f184,plain,(
    ~ r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f182,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f182,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ),
    inference(subsumption_resolution,[],[f181,f11])).

fof(f181,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
      | k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f172,f15])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f172,plain,(
    ! [X14] :
      ( r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k10_relat_1(sK0,k2_relat_1(sK0)))
      | k1_relat_1(sK0) = k10_relat_1(sK0,X14) ) ),
    inference(subsumption_resolution,[],[f166,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(sK0,X0),X1),sK0)
      | k1_relat_1(sK0) = X0
      | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0)))
      | k1_relat_1(sK0) = X0
      | ~ r2_hidden(k4_tarski(sK1(sK0,X0),X1),sK0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(resolution,[],[f135,f15])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0)))
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0)))
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(resolution,[],[f80,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),k2_relat_1(sK0))
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(resolution,[],[f29,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK0)
      | r2_hidden(X12,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f10,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK0,X0),X1)
      | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,X1))
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK0,X0),k2_relat_1(sK0))
      | ~ r2_hidden(sK3(sK0,X0),X1)
      | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,X1))
      | r2_hidden(sK1(sK0,X0),X0)
      | k1_relat_1(sK0) = X0 ) ),
    inference(resolution,[],[f27,f14])).

fof(f27,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X6),sK0)
      | ~ r2_hidden(X6,k2_relat_1(sK0))
      | ~ r2_hidden(X6,X8)
      | r2_hidden(X7,k10_relat_1(sK0,X8)) ) ),
    inference(resolution,[],[f10,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f166,plain,(
    ! [X14] :
      ( r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k10_relat_1(sK0,k2_relat_1(sK0)))
      | k1_relat_1(sK0) = k10_relat_1(sK0,X14)
      | r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,X14)),sK4(sK1(sK0,k10_relat_1(sK0,X14)),X14,sK0)),sK0) ) ),
    inference(resolution,[],[f135,f25])).

fof(f25,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k10_relat_1(sK0,X3))
      | r2_hidden(k4_tarski(X2,sK4(X2,X3,sK0)),sK0) ) ),
    inference(resolution,[],[f10,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f299,plain,(
    ! [X14] :
      ( r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k1_relat_1(sK0))
      | k1_relat_1(sK0) = k10_relat_1(sK0,X14) ) ),
    inference(subsumption_resolution,[],[f280,f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f280,plain,(
    ! [X14] :
      ( r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k1_relat_1(sK0))
      | k1_relat_1(sK0) = k10_relat_1(sK0,X14)
      | r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,X14)),sK4(sK1(sK0,k10_relat_1(sK0,X14)),X14,sK0)),sK0) ) ),
    inference(resolution,[],[f259,f25])).

fof(f259,plain,(
    ! [X10] :
      ( r2_hidden(sK1(sK0,X10),X10)
      | r2_hidden(sK1(sK0,X10),k1_relat_1(sK0))
      | k1_relat_1(sK0) = X10 ) ),
    inference(resolution,[],[f147,f23])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(sK0,X0),sK4(sK1(sK0,X0),k2_relat_1(sK0),sK0)),sK0)
      | k1_relat_1(sK0) = X0
      | r2_hidden(sK1(sK0,X0),X0) ) ),
    inference(resolution,[],[f135,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (10066)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.45  % (10066)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f312,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f300,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0] : (k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.46    inference(resolution,[],[f299,f184])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~r2_hidden(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.21/0.46    inference(resolution,[],[f182,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.46    inference(equality_resolution,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f181,f11])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) | k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f172,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ( ! [X14] : (r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k10_relat_1(sK0,k2_relat_1(sK0))) | k1_relat_1(sK0) = k10_relat_1(sK0,X14)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f166,f171])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(sK0,X0),X1),sK0) | k1_relat_1(sK0) = X0 | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0)))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0))) | k1_relat_1(sK0) = X0 | ~r2_hidden(k4_tarski(sK1(sK0,X0),X1),sK0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(resolution,[],[f135,f15])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0))) | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,k2_relat_1(sK0))) | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0 | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(resolution,[],[f80,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k2_relat_1(sK0)) | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(resolution,[],[f29,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X12,X11] : (~r2_hidden(k4_tarski(X11,X12),sK0) | r2_hidden(X12,k2_relat_1(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f10,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,X1)) | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f77,f30])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,X0),X1) | r2_hidden(sK1(sK0,X0),k10_relat_1(sK0,X1)) | r2_hidden(sK1(sK0,X0),X0) | k1_relat_1(sK0) = X0) )),
% 0.21/0.46    inference(resolution,[],[f27,f14])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X6,X8,X7] : (~r2_hidden(k4_tarski(X7,X6),sK0) | ~r2_hidden(X6,k2_relat_1(sK0)) | ~r2_hidden(X6,X8) | r2_hidden(X7,k10_relat_1(sK0,X8))) )),
% 0.21/0.46    inference(resolution,[],[f10,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ( ! [X14] : (r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k10_relat_1(sK0,k2_relat_1(sK0))) | k1_relat_1(sK0) = k10_relat_1(sK0,X14) | r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,X14)),sK4(sK1(sK0,k10_relat_1(sK0,X14)),X14,sK0)),sK0)) )),
% 0.21/0.46    inference(resolution,[],[f135,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~r2_hidden(X2,k10_relat_1(sK0,X3)) | r2_hidden(k4_tarski(X2,sK4(X2,X3,sK0)),sK0)) )),
% 0.21/0.46    inference(resolution,[],[f10,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f299,plain,(
% 0.21/0.46    ( ! [X14] : (r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k1_relat_1(sK0)) | k1_relat_1(sK0) = k10_relat_1(sK0,X14)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f280,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.46    inference(equality_resolution,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    ( ! [X14] : (r2_hidden(sK1(sK0,k10_relat_1(sK0,X14)),k1_relat_1(sK0)) | k1_relat_1(sK0) = k10_relat_1(sK0,X14) | r2_hidden(k4_tarski(sK1(sK0,k10_relat_1(sK0,X14)),sK4(sK1(sK0,k10_relat_1(sK0,X14)),X14,sK0)),sK0)) )),
% 0.21/0.46    inference(resolution,[],[f259,f25])).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    ( ! [X10] : (r2_hidden(sK1(sK0,X10),X10) | r2_hidden(sK1(sK0,X10),k1_relat_1(sK0)) | k1_relat_1(sK0) = X10) )),
% 0.21/0.46    inference(resolution,[],[f147,f23])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(k4_tarski(sK1(sK0,X0),sK4(sK1(sK0,X0),k2_relat_1(sK0),sK0)),sK0) | k1_relat_1(sK0) = X0 | r2_hidden(sK1(sK0,X0),X0)) )),
% 0.21/0.46    inference(resolution,[],[f135,f25])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (10066)------------------------------
% 0.21/0.46  % (10066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10066)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (10066)Memory used [KB]: 1791
% 0.21/0.46  % (10066)Time elapsed: 0.022 s
% 0.21/0.46  % (10066)------------------------------
% 0.21/0.46  % (10066)------------------------------
% 0.21/0.46  % (10052)Success in time 0.1 s
%------------------------------------------------------------------------------
