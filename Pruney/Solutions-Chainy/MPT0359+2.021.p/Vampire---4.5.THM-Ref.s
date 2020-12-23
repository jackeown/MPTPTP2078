%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:41 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 312 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   23
%              Number of atoms          :  197 ( 979 expanded)
%              Number of equality atoms :   68 ( 315 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f39])).

% (25996)Termination reason: Refutation not found, incomplete strategy

% (25996)Memory used [KB]: 6140
fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

% (25996)Time elapsed: 0.111 s
% (25996)------------------------------
% (25996)------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f235,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f217,f234])).

fof(f234,plain,(
    k1_xboole_0 = k3_subset_1(sK0,sK0) ),
    inference(forward_demodulation,[],[f227,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f227,plain,(
    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f142,f216])).

fof(f216,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( sK0 = sK1
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f208,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f208,plain,
    ( sK1 = k5_xboole_0(sK0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f196,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f146,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f146,plain,
    ( v1_xboole_0(k5_xboole_0(sK0,sK1))
    | sK0 = sK1 ),
    inference(resolution,[],[f144,f122])).

fof(f122,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | v1_xboole_0(k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f121,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f121,plain,(
    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f44,f99])).

fof(f99,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f47,f91])).

fof(f91,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f82,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f53,f76])).

fof(f76,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f75,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

% (25997)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f75,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f74,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f144,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f62,f142])).

fof(f62,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f36,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f196,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f175,f65])).

fof(f65,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f175,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f59,f41])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f142,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f140,f99])).

fof(f140,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f54,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f217,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f64,f216])).

fof(f64,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f63])).

% (25995)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f63,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f37,f40])).

fof(f37,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (25988)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (26004)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (25985)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.51  % (25989)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.52  % (25988)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % (25983)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (25996)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.53  % (25981)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (25996)Refutation not found, incomplete strategy% (25996)------------------------------
% 1.21/0.53  % (25996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f236,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(subsumption_resolution,[],[f235,f39])).
% 1.21/0.53  % (25996)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (25996)Memory used [KB]: 6140
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f6])).
% 1.21/0.53  % (25996)Time elapsed: 0.111 s
% 1.21/0.53  % (25996)------------------------------
% 1.21/0.53  % (25996)------------------------------
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.21/0.53  fof(f235,plain,(
% 1.21/0.53    ~r1_tarski(k1_xboole_0,sK0)),
% 1.21/0.53    inference(backward_demodulation,[],[f217,f234])).
% 1.21/0.53  fof(f234,plain,(
% 1.21/0.53    k1_xboole_0 = k3_subset_1(sK0,sK0)),
% 1.21/0.53    inference(forward_demodulation,[],[f227,f41])).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.21/0.53  fof(f227,plain,(
% 1.21/0.53    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)),
% 1.21/0.53    inference(backward_demodulation,[],[f142,f216])).
% 1.21/0.53  fof(f216,plain,(
% 1.21/0.53    sK0 = sK1),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f215])).
% 1.21/0.53  fof(f215,plain,(
% 1.21/0.53    sK0 = sK1 | sK0 = sK1),
% 1.21/0.53    inference(forward_demodulation,[],[f208,f42])).
% 1.21/0.53  fof(f42,plain,(
% 1.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.21/0.53    inference(cnf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.33/0.53  fof(f208,plain,(
% 1.33/0.53    sK1 = k5_xboole_0(sK0,k1_xboole_0) | sK0 = sK1),
% 1.33/0.53    inference(superposition,[],[f196,f150])).
% 1.33/0.53  fof(f150,plain,(
% 1.33/0.53    k1_xboole_0 = k5_xboole_0(sK0,sK1) | sK0 = sK1),
% 1.33/0.53    inference(resolution,[],[f146,f43])).
% 1.33/0.53  fof(f43,plain,(
% 1.33/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.33/0.53  fof(f146,plain,(
% 1.33/0.53    v1_xboole_0(k5_xboole_0(sK0,sK1)) | sK0 = sK1),
% 1.33/0.53    inference(resolution,[],[f144,f122])).
% 1.33/0.53  fof(f122,plain,(
% 1.33/0.53    ~r1_tarski(k5_xboole_0(sK0,sK1),sK1) | v1_xboole_0(k5_xboole_0(sK0,sK1))),
% 1.33/0.53    inference(resolution,[],[f121,f52])).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f23,plain,(
% 1.33/0.53    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.33/0.53    inference(flattening,[],[f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.33/0.53  fof(f121,plain,(
% 1.33/0.53    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.33/0.53    inference(superposition,[],[f44,f99])).
% 1.33/0.53  fof(f99,plain,(
% 1.33/0.53    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.33/0.53    inference(superposition,[],[f47,f91])).
% 1.33/0.53  fof(f91,plain,(
% 1.33/0.53    sK1 = k3_xboole_0(sK0,sK1)),
% 1.33/0.53    inference(superposition,[],[f82,f45])).
% 1.33/0.53  fof(f45,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.33/0.53  fof(f82,plain,(
% 1.33/0.53    sK1 = k3_xboole_0(sK1,sK0)),
% 1.33/0.53    inference(resolution,[],[f53,f76])).
% 1.33/0.53  fof(f76,plain,(
% 1.33/0.53    r1_tarski(sK1,sK0)),
% 1.33/0.53    inference(resolution,[],[f75,f61])).
% 1.33/0.53  fof(f61,plain,(
% 1.33/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.33/0.53    inference(equality_resolution,[],[f55])).
% 1.33/0.53  fof(f55,plain,(
% 1.33/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f34])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.53    inference(rectify,[],[f31])).
% 1.33/0.53  % (25997)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.53    inference(nnf_transformation,[],[f12])).
% 1.33/0.53  fof(f12,axiom,(
% 1.33/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.33/0.53  fof(f75,plain,(
% 1.33/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.33/0.53    inference(subsumption_resolution,[],[f74,f38])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f16])).
% 1.33/0.53  fof(f16,axiom,(
% 1.33/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.33/0.53  fof(f74,plain,(
% 1.33/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.33/0.53    inference(resolution,[],[f48,f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.33/0.53    inference(cnf_transformation,[],[f29])).
% 1.33/0.53  fof(f29,plain,(
% 1.33/0.53    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.53    inference(flattening,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.53    inference(nnf_transformation,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f18])).
% 1.33/0.53  fof(f18,negated_conjecture,(
% 1.33/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.33/0.53    inference(negated_conjecture,[],[f17])).
% 1.33/0.53  fof(f17,conjecture,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.33/0.53  fof(f48,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f30])).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.33/0.53    inference(nnf_transformation,[],[f21])).
% 1.33/0.53  fof(f21,plain,(
% 1.33/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f13])).
% 1.33/0.53  fof(f13,axiom,(
% 1.33/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.33/0.53  fof(f53,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f24])).
% 1.33/0.53  fof(f24,plain,(
% 1.33/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.33/0.53  fof(f47,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  fof(f9,axiom,(
% 1.33/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.33/0.53  fof(f144,plain,(
% 1.33/0.53    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 1.33/0.53    inference(backward_demodulation,[],[f62,f142])).
% 1.33/0.53  fof(f62,plain,(
% 1.33/0.53    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.33/0.53    inference(backward_demodulation,[],[f36,f40])).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f14])).
% 1.33/0.53  fof(f14,axiom,(
% 1.33/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.33/0.53  fof(f36,plain,(
% 1.33/0.53    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f29])).
% 1.33/0.53  fof(f196,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.33/0.53    inference(forward_demodulation,[],[f175,f65])).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.33/0.53    inference(superposition,[],[f46,f42])).
% 1.33/0.53  fof(f46,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.33/0.53  fof(f175,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.33/0.53    inference(superposition,[],[f59,f41])).
% 1.33/0.53  fof(f59,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f10])).
% 1.33/0.53  fof(f10,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.33/0.53  fof(f142,plain,(
% 1.33/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.33/0.53    inference(forward_demodulation,[],[f140,f99])).
% 1.33/0.53  fof(f140,plain,(
% 1.33/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.33/0.53    inference(resolution,[],[f54,f35])).
% 1.33/0.53  fof(f54,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f15])).
% 1.33/0.53  fof(f15,axiom,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.33/0.53  fof(f217,plain,(
% 1.33/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f64,f216])).
% 1.33/0.53  fof(f64,plain,(
% 1.33/0.53    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1),
% 1.33/0.53    inference(inner_rewriting,[],[f63])).
% 1.33/0.53  % (25995)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.53  fof(f63,plain,(
% 1.33/0.53    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.33/0.53    inference(backward_demodulation,[],[f37,f40])).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f29])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (25988)------------------------------
% 1.33/0.53  % (25988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (25988)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (25988)Memory used [KB]: 6396
% 1.33/0.53  % (25988)Time elapsed: 0.109 s
% 1.33/0.53  % (25988)------------------------------
% 1.33/0.53  % (25988)------------------------------
% 1.33/0.53  % (25980)Success in time 0.174 s
%------------------------------------------------------------------------------
