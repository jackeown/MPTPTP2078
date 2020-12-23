%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  70 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 401 expanded)
%              Number of equality atoms :   39 ( 205 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f16])).

fof(f16,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK2
    & k2_mcart_1(sK0) = k2_mcart_1(sK2)
    & k1_mcart_1(sK0) = k1_mcart_1(sK2)
    & r2_hidden(sK0,sK1)
    & r2_hidden(sK2,sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X0 != X2
            & k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK0 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK0)
          & k1_mcart_1(X2) = k1_mcart_1(sK0)
          & r2_hidden(sK0,sK1)
          & r2_hidden(X2,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( sK0 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK0)
        & k1_mcart_1(X2) = k1_mcart_1(sK0)
        & r2_hidden(sK0,sK1)
        & r2_hidden(X2,sK1) )
   => ( sK0 != sK2
      & k2_mcart_1(sK0) = k2_mcart_1(sK2)
      & k1_mcart_1(sK0) = k1_mcart_1(sK2)
      & r2_hidden(sK0,sK1)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f23,plain,(
    sK0 = sK2 ),
    inference(backward_demodulation,[],[f21,f22])).

fof(f22,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f11,f13,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f13,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(forward_demodulation,[],[f20,f14])).

fof(f14,plain,(
    k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK0)) ),
    inference(forward_demodulation,[],[f19,f15])).

fof(f15,plain,(
    k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f11,f12,f17])).

fof(f12,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 17:21:07 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.48  % (8763)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (8771)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (8756)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (8771)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f23,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    sK0 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    (sK0 != sK2 & k2_mcart_1(sK0) = k2_mcart_1(sK2) & k1_mcart_1(sK0) = k1_mcart_1(sK2) & r2_hidden(sK0,sK1) & r2_hidden(sK2,sK1)) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (X0 != X2 & k2_mcart_1(X0) = k2_mcart_1(X2) & k1_mcart_1(X0) = k1_mcart_1(X2) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) & v1_relat_1(X1)) => (? [X2] : (sK0 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK0) & k1_mcart_1(X2) = k1_mcart_1(sK0) & r2_hidden(sK0,sK1) & r2_hidden(X2,sK1)) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X2] : (sK0 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK0) & k1_mcart_1(X2) = k1_mcart_1(sK0) & r2_hidden(sK0,sK1) & r2_hidden(X2,sK1)) => (sK0 != sK2 & k2_mcart_1(sK0) = k2_mcart_1(sK2) & k1_mcart_1(sK0) = k1_mcart_1(sK2) & r2_hidden(sK0,sK1) & r2_hidden(sK2,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (X0 != X2 & k2_mcart_1(X0) = k2_mcart_1(X2) & k1_mcart_1(X0) = k1_mcart_1(X2) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f4])).
% 0.21/0.49  fof(f4,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (X0 != X2 & (k2_mcart_1(X0) = k2_mcart_1(X2) & k1_mcart_1(X0) = k1_mcart_1(X2) & r2_hidden(X0,X1) & r2_hidden(X2,X1))) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((k2_mcart_1(X0) = k2_mcart_1(X2) & k1_mcart_1(X0) = k1_mcart_1(X2) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) => X0 = X2))),
% 0.21/0.49    inference(negated_conjecture,[],[f2])).
% 0.21/0.49  fof(f2,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((k2_mcart_1(X0) = k2_mcart_1(X2) & k1_mcart_1(X0) = k1_mcart_1(X2) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) => X0 = X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    sK0 = sK2),
% 0.21/0.49    inference(backward_demodulation,[],[f21,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f11,f13,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK2 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f20,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    k1_mcart_1(sK0) = k1_mcart_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f19,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    k2_mcart_1(sK0) = k2_mcart_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f11,f12,f17])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r2_hidden(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8771)------------------------------
% 0.21/0.49  % (8771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8771)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8771)Memory used [KB]: 6012
% 0.21/0.49  % (8771)Time elapsed: 0.065 s
% 0.21/0.49  % (8771)------------------------------
% 0.21/0.49  % (8771)------------------------------
% 0.21/0.50  % (8755)Success in time 0.122 s
%------------------------------------------------------------------------------
