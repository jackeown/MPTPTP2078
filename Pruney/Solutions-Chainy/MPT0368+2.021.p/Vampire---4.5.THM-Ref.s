%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 116 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 ( 425 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f31])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f239,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f238,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f238,plain,(
    sK1 = k2_subset_1(sK0) ),
    inference(subsumption_resolution,[],[f237,f117])).

fof(f117,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f95,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0] :
      ( r2_xboole_0(sK1,X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f70,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f69,plain,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    r1_tarski(sK1,sK0) ),
    inference(forward_demodulation,[],[f62,f34])).

fof(f34,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f62,plain,(
    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f58,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f237,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK1 = k2_subset_1(sK0) ),
    inference(forward_demodulation,[],[f233,f33])).

fof(f233,plain,
    ( r2_xboole_0(k2_subset_1(sK0),sK1)
    | sK1 = k2_subset_1(sK0) ),
    inference(resolution,[],[f140,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_xboole_0(X0,sK1)
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f137,f89])).

fof(f89,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(sK0,X2,sK1),sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | r2_xboole_0(X2,sK1)
      | sK1 = X2 ) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X5] :
      ( r1_tarski(X5,sK1)
      | ~ r2_hidden(sK2(sK0,X5,sK1),sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK2(X0,X1,X2),X2)
            & r2_hidden(sK2(X0,X1,X2),X1)
            & m1_subset_1(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_xboole_0(X0,sK1)
      | sK1 = X0
      | r2_hidden(sK2(sK0,X0,sK1),sK1) ) ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(sK0,X2,sK1),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | r2_xboole_0(X2,sK1)
      | sK1 = X2 ) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK1)
      | m1_subset_1(sK2(sK0,X1,sK1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (11358)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.45  % (11358)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (11354)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (11354)Refutation not found, incomplete strategy% (11354)------------------------------
% 0.21/0.46  % (11354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (11354)Memory used [KB]: 6140
% 0.21/0.46  % (11354)Time elapsed: 0.032 s
% 0.21/0.46  % (11354)------------------------------
% 0.21/0.46  % (11354)------------------------------
% 0.21/0.47  % (11373)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f239,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    sK0 = sK1),
% 0.21/0.47    inference(forward_demodulation,[],[f238,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    sK1 = k2_subset_1(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f237,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f95,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f78,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0] : (r2_xboole_0(sK1,X0) | ~r1_tarski(sK0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f70,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_xboole_0(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f31])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    r2_xboole_0(sK1,sK0) | sK0 = sK1),
% 0.21/0.47    inference(resolution,[],[f64,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    r1_tarski(sK1,sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f62,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(resolution,[],[f58,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f29,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    r2_xboole_0(sK0,sK1) | sK1 = k2_subset_1(sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f233,f33])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    r2_xboole_0(k2_subset_1(sK0),sK1) | sK1 = k2_subset_1(sK0)),
% 0.21/0.47    inference(resolution,[],[f140,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_xboole_0(X0,sK1) | sK1 = X0) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X2] : (~r2_hidden(sK2(sK0,X2,sK1),sK1) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_xboole_0(X2,sK1) | sK1 = X2) )),
% 0.21/0.47    inference(resolution,[],[f55,f47])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X5] : (r1_tarski(X5,sK1) | ~r2_hidden(sK2(sK0,X5,sK1),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(sK0))) )),
% 0.21/0.47    inference(resolution,[],[f29,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_xboole_0(X0,sK1) | sK1 = X0 | r2_hidden(sK2(sK0,X0,sK1),sK1)) )),
% 0.21/0.47    inference(resolution,[],[f77,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X2] : (m1_subset_1(sK2(sK0,X2,sK1),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_xboole_0(X2,sK1) | sK1 = X2) )),
% 0.21/0.47    inference(resolution,[],[f51,f47])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(X1,sK1) | m1_subset_1(sK2(sK0,X1,sK1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.21/0.47    inference(resolution,[],[f29,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11358)------------------------------
% 0.21/0.47  % (11358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11358)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11358)Memory used [KB]: 1663
% 0.21/0.47  % (11358)Time elapsed: 0.063 s
% 0.21/0.47  % (11358)------------------------------
% 0.21/0.47  % (11358)------------------------------
% 0.21/0.48  % (11353)Success in time 0.119 s
%------------------------------------------------------------------------------
