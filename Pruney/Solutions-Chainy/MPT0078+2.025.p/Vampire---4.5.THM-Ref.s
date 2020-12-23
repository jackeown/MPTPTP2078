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
% DateTime   : Thu Dec  3 12:30:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 258 expanded)
%              Number of leaves         :   12 (  77 expanded)
%              Depth                    :   27
%              Number of atoms          :  107 ( 582 expanded)
%              Number of equality atoms :   61 ( 342 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f581,plain,(
    $false ),
    inference(subsumption_resolution,[],[f580,f25])).

fof(f25,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f580,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f579,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f579,plain,(
    sK2 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f578,f38])).

fof(f38,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f35,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f23,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f578,plain,(
    sK2 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f574,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f574,plain,(
    sK2 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f569,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f569,plain,(
    ! [X0] : sK2 = k4_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f568,f74])).

fof(f74,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f68,f27])).

fof(f68,plain,(
    ! [X1] : k4_xboole_0(sK2,X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X1)) ),
    inference(backward_demodulation,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[],[f55,f30])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(sK2,k3_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,X0) ),
    inference(forward_demodulation,[],[f53,f26])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(sK2,k3_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[],[f34,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f29,f22])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f54,plain,(
    ! [X1] : k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f34,f44])).

fof(f568,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f563,f30])).

fof(f563,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[],[f134,f29])).

fof(f134,plain,(
    ! [X0] : k4_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(superposition,[],[f34,f105])).

fof(f105,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f72,f104])).

fof(f104,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f103,f27])).

fof(f103,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f102,f48])).

fof(f48,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f28])).

fof(f37,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f36,f30])).

fof(f36,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f33])).

fof(f24,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f98,f30])).

fof(f98,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f60,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(backward_demodulation,[],[f79,f80])).

fof(f80,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f29,f74])).

fof(f79,plain,(
    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f31,f74])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f34,f45])).

fof(f45,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f43,f31])).

fof(f43,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f31,f22])).

fof(f72,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f68,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (25845)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.43  % (25845)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f581,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f580,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    sK0 != sK2),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.43    inference(negated_conjecture,[],[f9])).
% 0.21/0.43  fof(f9,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.21/0.43  fof(f580,plain,(
% 0.21/0.43    sK0 = sK2),
% 0.21/0.43    inference(forward_demodulation,[],[f579,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f579,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f578,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f35,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) )),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f23,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f578,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.43    inference(forward_demodulation,[],[f574,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f574,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 0.21/0.43    inference(superposition,[],[f569,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.43  fof(f569,plain,(
% 0.21/0.43    ( ! [X0] : (sK2 = k4_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK0,X0)))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f568,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.43    inference(superposition,[],[f68,f27])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X1] : (k4_xboole_0(sK2,X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X1))) )),
% 0.21/0.43    inference(backward_demodulation,[],[f54,f64])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X0))) )),
% 0.21/0.43    inference(superposition,[],[f55,f30])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK2,k3_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK2,X0)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f53,f26])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK2,k3_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0)) )),
% 0.21/0.43    inference(superposition,[],[f34,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.43    inference(superposition,[],[f29,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X1] : (k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X1))) )),
% 0.21/0.43    inference(superposition,[],[f34,f44])).
% 0.21/0.43  fof(f568,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(sK0,X0)))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f563,f30])).
% 0.21/0.43  fof(f563,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,X0),sK1))) )),
% 0.21/0.43    inference(superposition,[],[f134,f29])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 0.21/0.43    inference(superposition,[],[f34,f105])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(backward_demodulation,[],[f72,f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.43    inference(forward_demodulation,[],[f103,f27])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f102,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f37,f28])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f36,f30])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK1))) )),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f24,f33])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(forward_demodulation,[],[f98,f30])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k3_xboole_0(sK2,sK1))),
% 0.21/0.43    inference(superposition,[],[f60,f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.21/0.43    inference(backward_demodulation,[],[f79,f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.43    inference(superposition,[],[f29,f74])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2)),
% 0.21/0.43    inference(superposition,[],[f31,f74])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK0,sK1))) )),
% 0.21/0.43    inference(superposition,[],[f34,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(forward_demodulation,[],[f43,f31])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.43    inference(superposition,[],[f31,f22])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.43    inference(superposition,[],[f68,f45])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (25845)------------------------------
% 0.21/0.43  % (25845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (25845)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (25845)Memory used [KB]: 6524
% 0.21/0.43  % (25845)Time elapsed: 0.017 s
% 0.21/0.43  % (25845)------------------------------
% 0.21/0.43  % (25845)------------------------------
% 0.21/0.44  % (25829)Success in time 0.084 s
%------------------------------------------------------------------------------
