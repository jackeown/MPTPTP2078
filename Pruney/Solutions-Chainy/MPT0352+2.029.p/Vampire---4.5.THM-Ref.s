%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:18 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 207 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 860 expanded)
%              Number of equality atoms :   30 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f568,plain,(
    $false ),
    inference(subsumption_resolution,[],[f567,f351])).

fof(f351,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f346,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f346,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f345,f339])).

fof(f339,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
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

fof(f345,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f31,f338])).

fof(f338,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f567,plain,(
    r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f551,f437])).

fof(f437,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f403,f47])).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f403,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f50,f62])).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f61,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f58,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f551,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f359,f426])).

fof(f426,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f402,f47])).

fof(f402,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f50,f60])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f57,f52])).

fof(f57,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f44])).

fof(f55,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f28])).

fof(f359,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f350,f351])).

fof(f350,plain,(
    ! [X3] :
      ( r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(sK0,sK2)))
      | r1_tarski(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f341,f339])).

fof(f341,plain,(
    ! [X3] :
      ( r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k3_subset_1(sK0,sK2)))
      | r1_tarski(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f68,f338])).

fof(f68,plain,(
    ! [X3] :
      ( r1_tarski(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k4_xboole_0(X3,k3_subset_1(sK0,sK2)))
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:49:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.46  % (1425)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.46  % (1405)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.46  % (1411)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.47  % (1403)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.48  % (1401)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.48  % (1413)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.48  % (1429)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.49  % (1409)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.49  % (1400)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.49  % (1421)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.49  % (1417)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.49  % (1417)Refutation not found, incomplete strategy% (1417)------------------------------
% 0.18/0.49  % (1417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (1417)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (1417)Memory used [KB]: 10618
% 0.18/0.49  % (1417)Time elapsed: 0.121 s
% 0.18/0.49  % (1417)------------------------------
% 0.18/0.49  % (1417)------------------------------
% 0.18/0.49  % (1404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.49  % (1405)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f568,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(subsumption_resolution,[],[f567,f351])).
% 0.18/0.49  fof(f351,plain,(
% 0.18/0.49    ~r1_tarski(sK1,sK2)),
% 0.18/0.49    inference(subsumption_resolution,[],[f346,f33])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.18/0.49  fof(f346,plain,(
% 0.18/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.18/0.49    inference(backward_demodulation,[],[f345,f339])).
% 0.18/0.49  fof(f339,plain,(
% 0.18/0.49    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.18/0.49    inference(resolution,[],[f32,f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.49    inference(flattening,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.49    inference(nnf_transformation,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,negated_conjecture,(
% 0.18/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.18/0.49    inference(negated_conjecture,[],[f11])).
% 0.18/0.49  fof(f11,conjecture,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f14])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.18/0.49  fof(f345,plain,(
% 0.18/0.49    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.18/0.49    inference(backward_demodulation,[],[f31,f338])).
% 0.18/0.49  fof(f338,plain,(
% 0.18/0.49    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.18/0.49    inference(resolution,[],[f32,f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f567,plain,(
% 0.18/0.49    r1_tarski(sK1,sK2)),
% 0.18/0.49    inference(forward_demodulation,[],[f551,f437])).
% 0.18/0.49  fof(f437,plain,(
% 0.18/0.49    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.18/0.49    inference(forward_demodulation,[],[f403,f47])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.18/0.49  fof(f403,plain,(
% 0.18/0.49    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.18/0.49    inference(superposition,[],[f50,f62])).
% 0.18/0.49  fof(f62,plain,(
% 0.18/0.49    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.18/0.49    inference(resolution,[],[f61,f35])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.18/0.49    inference(nnf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.18/0.49  fof(f61,plain,(
% 0.18/0.49    r1_tarski(sK2,sK0)),
% 0.18/0.49    inference(resolution,[],[f58,f52])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.18/0.49    inference(equality_resolution,[],[f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.49    inference(rectify,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.49    inference(nnf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.18/0.49  fof(f58,plain,(
% 0.18/0.49    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(subsumption_resolution,[],[f56,f44])).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,axiom,(
% 0.18/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.18/0.49  fof(f56,plain,(
% 0.18/0.49    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(resolution,[],[f40,f29])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.18/0.49    inference(nnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f46,f45,f45])).
% 0.18/0.49  fof(f45,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.49  fof(f551,plain,(
% 0.18/0.49    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 0.18/0.49    inference(superposition,[],[f359,f426])).
% 0.18/0.49  fof(f426,plain,(
% 0.18/0.49    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.18/0.49    inference(forward_demodulation,[],[f402,f47])).
% 0.18/0.49  fof(f402,plain,(
% 0.18/0.49    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.18/0.49    inference(superposition,[],[f50,f60])).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.18/0.49    inference(resolution,[],[f59,f35])).
% 0.18/0.49  fof(f59,plain,(
% 0.18/0.49    r1_tarski(sK1,sK0)),
% 0.18/0.49    inference(resolution,[],[f57,f52])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(subsumption_resolution,[],[f55,f44])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.18/0.49    inference(resolution,[],[f40,f28])).
% 0.18/0.49  fof(f359,plain,(
% 0.18/0.49    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(sK0,sK2)))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f350,f351])).
% 0.18/0.49  fof(f350,plain,(
% 0.18/0.49    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k4_xboole_0(sK0,sK2))) | r1_tarski(sK1,sK2)) )),
% 0.18/0.49    inference(backward_demodulation,[],[f341,f339])).
% 0.18/0.49  fof(f341,plain,(
% 0.18/0.49    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k4_xboole_0(X3,k3_subset_1(sK0,sK2))) | r1_tarski(sK1,sK2)) )),
% 0.18/0.49    inference(backward_demodulation,[],[f68,f338])).
% 0.18/0.49  fof(f68,plain,(
% 0.18/0.49    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k4_xboole_0(X3,k3_subset_1(sK0,sK2))) | r1_tarski(sK1,sK2)) )),
% 0.18/0.49    inference(resolution,[],[f33,f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (1405)------------------------------
% 0.18/0.49  % (1405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (1405)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (1405)Memory used [KB]: 6524
% 0.18/0.49  % (1405)Time elapsed: 0.121 s
% 0.18/0.49  % (1405)------------------------------
% 0.18/0.49  % (1405)------------------------------
% 0.18/0.49  % (1427)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.50  % (1410)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.50  % (1399)Success in time 0.156 s
%------------------------------------------------------------------------------
