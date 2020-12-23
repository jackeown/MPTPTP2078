%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 433 expanded)
%              Number of leaves         :    8 ( 109 expanded)
%              Depth                    :   23
%              Number of atoms          :  139 (1285 expanded)
%              Number of equality atoms :   25 ( 246 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f350])).

fof(f350,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(subsumption_resolution,[],[f348,f281])).

fof(f281,plain,(
    ! [X0,X1] : r1_tarski(X0,X1) ),
    inference(subsumption_resolution,[],[f28,f199])).

fof(f199,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,X1) ),
    inference(subsumption_resolution,[],[f198,f77])).

fof(f77,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(condensation,[],[f64])).

fof(f64,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK1,X4)
      | r1_tarski(sK1,X5)
      | r2_hidden(sK2(sK1,X5),sK0) ) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(sK1,X0),sK2(sK1,X1)),k2_zfmisc_1(sK0,sK0))
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X1) ) ),
    inference(superposition,[],[f40,f22])).

fof(f22,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK0 != sK1
      & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK2(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X0,X1)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK2(X2,X3),X0),k2_zfmisc_1(X2,X1))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f27,f28])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f197,f23])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK0 = sK1
      | ~ r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f191,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(sK1,sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f162,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f162,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,sK0),sK1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f151,f149])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(sK3(sK1,sK0),sK1) ) ),
    inference(resolution,[],[f134,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f134,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK3(sK1,sK0),X5),k2_zfmisc_1(sK0,X6))
      | ~ r2_hidden(X5,X6) ) ),
    inference(subsumption_resolution,[],[f132,f23])).

fof(f132,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK3(sK1,sK0),X5),k2_zfmisc_1(sK0,X6))
      | ~ r2_hidden(X5,X6)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f39,f77])).

fof(f39,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X6,X7)
      | r2_hidden(k4_tarski(sK3(X6,X7),X4),k2_zfmisc_1(X7,X5))
      | ~ r2_hidden(X4,X5)
      | X6 = X7 ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(sK1,sK0),sK0)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f134,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f348,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f24,f285])).

fof(f285,plain,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X1) ),
    inference(subsumption_resolution,[],[f30,f199])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:12:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (26151)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.48  % (26168)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.49  % (26161)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (26151)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (26168)Refutation not found, incomplete strategy% (26168)------------------------------
% 0.22/0.50  % (26168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26168)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26168)Memory used [KB]: 1663
% 0.22/0.50  % (26168)Time elapsed: 0.095 s
% 0.22/0.50  % (26168)------------------------------
% 0.22/0.50  % (26168)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f23,f350])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f348,f281])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f28,f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f198,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f70,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.22/0.50    inference(condensation,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r1_tarski(sK1,X4) | r1_tarski(sK1,X5) | r2_hidden(sK2(sK1,X5),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f48,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(nnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0),sK2(sK1,X1)),k2_zfmisc_1(sK0,sK0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X1)) )),
% 0.22/0.51    inference(superposition,[],[f40,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)) => (sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK2(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X0,X1) | r1_tarski(X2,X3)) )),
% 0.22/0.51    inference(resolution,[],[f38,f28])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK2(X2,X3),X0),k2_zfmisc_1(X2,X1)) | r1_tarski(X2,X3)) )),
% 0.22/0.51    inference(resolution,[],[f27,f28])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(sK1,sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f197,f23])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sK0 = sK1 | ~r1_tarski(sK1,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f191,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_xboole_0(sK1,sK0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f162,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK1,sK0),sK1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f151,f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(sK3(sK1,sK0),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f134,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1)) )),
% 0.22/0.51    inference(superposition,[],[f25,f22])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X6,X5] : (r2_hidden(k4_tarski(sK3(sK1,sK0),X5),k2_zfmisc_1(sK0,X6)) | ~r2_hidden(X5,X6)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f23])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X6,X5] : (r2_hidden(k4_tarski(sK3(sK1,sK0),X5),k2_zfmisc_1(sK0,X6)) | ~r2_hidden(X5,X6) | sK0 = sK1) )),
% 0.22/0.51    inference(resolution,[],[f39,f77])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X6,X4,X7,X5] : (~r1_tarski(X6,X7) | r2_hidden(k4_tarski(sK3(X6,X7),X4),k2_zfmisc_1(X7,X5)) | ~r2_hidden(X4,X5) | X6 = X7) )),
% 0.22/0.51    inference(resolution,[],[f27,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.51    inference(resolution,[],[f24,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X4,X5] : (r2_hidden(sK3(sK1,sK0),sK0) | ~r2_hidden(X4,X5)) )),
% 0.22/0.51    inference(resolution,[],[f134,f25])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f24,f285])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f30,f199])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26151)------------------------------
% 0.22/0.51  % (26151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26151)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26151)Memory used [KB]: 6524
% 0.22/0.51  % (26151)Time elapsed: 0.092 s
% 0.22/0.51  % (26151)------------------------------
% 0.22/0.51  % (26151)------------------------------
% 0.22/0.51  % (26141)Success in time 0.142 s
%------------------------------------------------------------------------------
