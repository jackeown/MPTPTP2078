%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 141 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  148 ( 505 expanded)
%              Number of equality atoms :   76 ( 278 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(X0)
      | r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f34,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f77,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f75,f64])).

fof(f64,plain,(
    sK1 = sK3 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( sK1 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,
    ( r2_hidden(sK1,k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | sK1 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 = X3 ) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) != k1_tarski(X2)
      | ~ r2_hidden(X2,k1_tarski(X3))
      | X2 = X3 ) ),
    inference(superposition,[],[f46,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f73,f65])).

fof(f65,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | ~ r2_hidden(sK0,k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | ~ r2_hidden(sK0,k1_tarski(sK2))
    | sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK1,k1_tarski(sK3))
    | ~ r2_hidden(sK0,k1_tarski(sK2))
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f47,f65])).

fof(f47,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | ~ r2_hidden(sK0,k1_tarski(sK2))
    | sK0 != sK2
    | sK1 != sK3 ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (28227)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.48  % (28220)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.48  % (28227)Refutation not found, incomplete strategy% (28227)------------------------------
% 0.21/0.48  % (28227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28227)Memory used [KB]: 10746
% 0.21/0.48  % (28227)Time elapsed: 0.082 s
% 0.21/0.48  % (28227)------------------------------
% 0.21/0.48  % (28227)------------------------------
% 0.21/0.50  % (28226)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (28226)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) != k1_tarski(X0) | r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f34,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f35,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f75,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK1 = sK3),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    sK1 = sK3 | sK1 = sK3),
% 0.21/0.50    inference(resolution,[],[f55,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_tarski(sK3)) | sK1 = sK3),
% 0.21/0.50    inference(resolution,[],[f32,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) | sK1 = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    (sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))))) => ((sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 = X3) )),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_tarski(X2) != k1_tarski(X2) | ~r2_hidden(X2,k1_tarski(X3)) | X2 = X3) )),
% 0.21/0.50    inference(superposition,[],[f46,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(superposition,[],[f27,f22])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_tarski(sK3))),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f44])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_tarski(sK0)) | ~r2_hidden(sK1,k1_tarski(sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f73,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    sK0 = sK2),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    sK0 = sK2 | sK0 = sK2),
% 0.21/0.50    inference(resolution,[],[f55,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r2_hidden(sK0,k1_tarski(sK2)) | sK0 = sK2),
% 0.21/0.50    inference(resolution,[],[f31,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) | sK0 = sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_tarski(sK3)) | ~r2_hidden(sK0,k1_tarski(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f55])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_tarski(sK3)) | ~r2_hidden(sK0,k1_tarski(sK2)) | sK1 != sK3),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    sK0 != sK0 | ~r2_hidden(sK1,k1_tarski(sK3)) | ~r2_hidden(sK0,k1_tarski(sK2)) | sK1 != sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f47,f65])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_tarski(sK3)) | ~r2_hidden(sK0,k1_tarski(sK2)) | sK0 != sK2 | sK1 != sK3),
% 0.21/0.50    inference(resolution,[],[f33,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) | sK0 != sK2 | sK1 != sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28226)------------------------------
% 0.21/0.50  % (28226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28226)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28226)Memory used [KB]: 1791
% 0.21/0.50  % (28226)Time elapsed: 0.096 s
% 0.21/0.50  % (28226)------------------------------
% 0.21/0.50  % (28226)------------------------------
% 0.21/0.50  % (28216)Success in time 0.147 s
%------------------------------------------------------------------------------
