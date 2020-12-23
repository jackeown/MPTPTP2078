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
% DateTime   : Thu Dec  3 12:44:30 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 461 expanded)
%              Number of leaves         :   12 ( 113 expanded)
%              Depth                    :   21
%              Number of atoms          :  219 (1955 expanded)
%              Number of equality atoms :   46 ( 460 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f99])).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_xboole_0,sK0),X0) ),
    inference(forward_demodulation,[],[f94,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (12811)Refutation not found, incomplete strategy% (12811)------------------------------
% (12811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12811)Termination reason: Refutation not found, incomplete strategy

% (12811)Memory used [KB]: 10618
% (12811)Time elapsed: 0.126 s
% (12811)------------------------------
% (12811)------------------------------
fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f85,plain,(
    r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f83,f37])).

fof(f83,plain,(
    ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f81,f76])).

fof(f76,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f61,f54])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | r2_hidden(X0,k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

% (12805)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f12,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f34,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f60,f76])).

fof(f60,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f56,f58])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f35,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X1] : r2_hidden(sK3(k1_xboole_0,sK0),X1) ),
    inference(subsumption_resolution,[],[f95,f99])).

fof(f95,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(k1_xboole_0,X1))
      | r2_hidden(sK3(k1_xboole_0,sK0),X1) ) ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.15/0.52  % (12812)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.15/0.52  % (12824)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.52  % (12816)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (12807)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (12802)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (12824)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (12811)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.53  % (12808)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f101,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(subsumption_resolution,[],[f100,f99])).
% 1.29/0.53  fof(f99,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0,sK0),X0)) )),
% 1.29/0.53    inference(forward_demodulation,[],[f94,f37])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.29/0.53  fof(f94,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(X0,k1_xboole_0))) )),
% 1.29/0.53    inference(resolution,[],[f85,f54])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.29/0.53    inference(equality_resolution,[],[f48])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.29/0.53    inference(cnf_transformation,[],[f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  % (12811)Refutation not found, incomplete strategy% (12811)------------------------------
% 1.29/0.53  % (12811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (12811)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (12811)Memory used [KB]: 10618
% 1.29/0.53  % (12811)Time elapsed: 0.126 s
% 1.29/0.53  % (12811)------------------------------
% 1.29/0.53  % (12811)------------------------------
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(rectify,[],[f29])).
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(flattening,[],[f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.29/0.53    inference(nnf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    r2_hidden(sK3(k1_xboole_0,sK0),k1_xboole_0)),
% 1.29/0.53    inference(resolution,[],[f84,f45])).
% 1.29/0.53  fof(f45,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.53    inference(rectify,[],[f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.53    inference(nnf_transformation,[],[f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.53  fof(f84,plain,(
% 1.29/0.53    ~r1_tarski(k1_xboole_0,sK0)),
% 1.29/0.53    inference(forward_demodulation,[],[f83,f37])).
% 1.29/0.53  fof(f83,plain,(
% 1.29/0.53    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.29/0.53    inference(forward_demodulation,[],[f81,f76])).
% 1.29/0.53  fof(f76,plain,(
% 1.29/0.53    k1_xboole_0 = sK1),
% 1.29/0.53    inference(subsumption_resolution,[],[f67,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.29/0.53  fof(f67,plain,(
% 1.29/0.53    k1_xboole_0 = sK1 | v1_xboole_0(sK1)),
% 1.29/0.53    inference(resolution,[],[f65,f40])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(rectify,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.29/0.53  fof(f65,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f61,f54])).
% 1.29/0.53  fof(f61,plain,(
% 1.29/0.53    ( ! [X0] : (k1_xboole_0 = sK1 | r2_hidden(X0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 1.29/0.53    inference(resolution,[],[f59,f44])).
% 1.29/0.53  fof(f44,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f27])).
% 1.29/0.53  fof(f59,plain,(
% 1.29/0.53    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.29/0.53    inference(backward_demodulation,[],[f57,f58])).
% 1.29/0.53  fof(f58,plain,(
% 1.29/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.29/0.53    inference(resolution,[],[f33,f43])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(flattening,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f12])).
% 1.29/0.53  % (12805)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.29/0.53    inference(negated_conjecture,[],[f10])).
% 1.29/0.53  fof(f10,conjecture,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.29/0.53  fof(f57,plain,(
% 1.29/0.53    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.29/0.53    inference(forward_demodulation,[],[f34,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f81,plain,(
% 1.29/0.53    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 1.29/0.53    inference(trivial_inequality_removal,[],[f79])).
% 1.29/0.53  fof(f79,plain,(
% 1.29/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 1.29/0.53    inference(backward_demodulation,[],[f60,f76])).
% 1.29/0.53  fof(f60,plain,(
% 1.29/0.53    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 != sK1),
% 1.29/0.53    inference(backward_demodulation,[],[f56,f58])).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.29/0.53    inference(forward_demodulation,[],[f35,f36])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f100,plain,(
% 1.29/0.53    ( ! [X1] : (r2_hidden(sK3(k1_xboole_0,sK0),X1)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f95,f99])).
% 1.29/0.53  fof(f95,plain,(
% 1.29/0.53    ( ! [X1] : (r2_hidden(sK3(k1_xboole_0,sK0),k4_xboole_0(k1_xboole_0,X1)) | r2_hidden(sK3(k1_xboole_0,sK0),X1)) )),
% 1.29/0.53    inference(resolution,[],[f85,f53])).
% 1.29/0.53  fof(f53,plain,(
% 1.29/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.29/0.53    inference(equality_resolution,[],[f49])).
% 1.29/0.53  fof(f49,plain,(
% 1.29/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.29/0.53    inference(cnf_transformation,[],[f32])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (12824)------------------------------
% 1.29/0.53  % (12824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (12824)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (12824)Memory used [KB]: 1791
% 1.29/0.53  % (12824)Time elapsed: 0.076 s
% 1.29/0.53  % (12824)------------------------------
% 1.29/0.53  % (12824)------------------------------
% 1.29/0.54  % (12800)Success in time 0.167 s
%------------------------------------------------------------------------------
