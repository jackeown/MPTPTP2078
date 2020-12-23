%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 208 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :   89 ( 460 expanded)
%              Number of equality atoms :   67 ( 389 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f104])).

fof(f104,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(subsumption_resolution,[],[f101,f100])).

fof(f100,plain,(
    ! [X0,X1] : r2_hidden(X0,X1) ),
    inference(subsumption_resolution,[],[f96,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f29,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_tarski(X0,X0) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X0))
      | k1_xboole_0 = k2_tarski(X0,X0) ) ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,(
    k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f50,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f50,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f20,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f46,f15])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) ),
    inference(superposition,[],[f20,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f14,f17,f17])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
      | k2_tarski(X0,X1) = k2_tarski(X2,X2) ) ),
    inference(definition_unfolding,[],[f23,f17,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
      | k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k1_tarski(X2)
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f100,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f15,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12844)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (12850)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (12850)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(superposition,[],[f29,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_tarski(X0,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) | k1_xboole_0 = k2_tarski(X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f33,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.51    inference(superposition,[],[f20,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f46,f15])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))),
% 0.21/0.51    inference(superposition,[],[f20,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))),
% 0.21/0.51    inference(definition_unfolding,[],[f14,f17,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)) | k2_tarski(X0,X1) = k2_tarski(X2,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f17,f17])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) | k2_tarski(X0,X1) = k1_tarski(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k1_tarski(X2) | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(resolution,[],[f100,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != X0) )),
% 0.21/0.51    inference(superposition,[],[f15,f104])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12850)------------------------------
% 0.21/0.51  % (12850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12850)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12850)Memory used [KB]: 6268
% 0.21/0.51  % (12850)Time elapsed: 0.094 s
% 0.21/0.51  % (12850)------------------------------
% 0.21/0.51  % (12850)------------------------------
% 0.21/0.51  % (12843)Success in time 0.149 s
%------------------------------------------------------------------------------
