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
% DateTime   : Thu Dec  3 12:44:37 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 708 expanded)
%              Number of leaves         :   11 ( 171 expanded)
%              Depth                    :   23
%              Number of atoms          :  224 (3037 expanded)
%              Number of equality atoms :   83 ( 978 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(subsumption_resolution,[],[f511,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f511,plain,(
    ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f509,f465])).

fof(f465,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f462])).

fof(f462,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f240,f211])).

fof(f211,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f207,f102])).

fof(f102,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f97,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f43,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
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

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f26,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f26,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

% (19292)Refutation not found, incomplete strategy% (19292)------------------------------
% (19292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19303)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (19292)Termination reason: Refutation not found, incomplete strategy

% (19292)Memory used [KB]: 1663
% (19292)Time elapsed: 0.110 s
% (19292)------------------------------
% (19292)------------------------------
fof(f207,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f44,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f179,f36])).

fof(f179,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f31,f120])).

fof(f120,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f32,f52])).

fof(f52,plain,
    ( sK1 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

% (19319)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f240,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,sK1,X0),X0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f228,f219])).

% (19294)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f219,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X8,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f211,f99])).

fof(f99,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f45,f51])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

% (19302)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f228,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = sK1
      | r2_hidden(sK2(k1_xboole_0,sK1,X0),k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,sK1,X0),X0) ) ),
    inference(superposition,[],[f210,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f210,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f193,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f120,f51])).

fof(f509,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f50,f465])).

fof(f50,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f46,f48])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f27,f29])).

fof(f27,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:10:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (19315)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (19307)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (19307)Refutation not found, incomplete strategy% (19307)------------------------------
% 0.21/0.49  % (19307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19307)Memory used [KB]: 6140
% 0.21/0.49  % (19307)Time elapsed: 0.003 s
% 0.21/0.49  % (19307)------------------------------
% 0.21/0.49  % (19307)------------------------------
% 0.21/0.49  % (19299)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (19296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.51  % (19305)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.51  % (19292)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.51  % (19293)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.51  % (19295)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.51  % (19316)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.21/0.52  % (19315)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f512,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(subsumption_resolution,[],[f511,f28])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f5])).
% 1.21/0.52  fof(f5,axiom,(
% 1.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.21/0.52  fof(f511,plain,(
% 1.21/0.52    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.21/0.52    inference(forward_demodulation,[],[f509,f465])).
% 1.21/0.52  fof(f465,plain,(
% 1.21/0.52    k1_xboole_0 = sK1),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f462])).
% 1.21/0.52  fof(f462,plain,(
% 1.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.21/0.52    inference(resolution,[],[f240,f211])).
% 1.21/0.52  fof(f211,plain,(
% 1.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(subsumption_resolution,[],[f207,f102])).
% 1.21/0.52  fof(f102,plain,(
% 1.21/0.52    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(subsumption_resolution,[],[f97,f44])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.21/0.52    inference(equality_resolution,[],[f38])).
% 1.21/0.52  fof(f38,plain,(
% 1.21/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f24])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f22,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.21/0.52    inference(rectify,[],[f21])).
% 1.21/0.52  fof(f21,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.21/0.52    inference(flattening,[],[f20])).
% 1.21/0.52  fof(f20,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.21/0.52    inference(nnf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.21/0.52  fof(f97,plain,(
% 1.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X3,sK1) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(superposition,[],[f43,f51])).
% 1.21/0.52  fof(f51,plain,(
% 1.21/0.52    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(resolution,[],[f49,f36])).
% 1.21/0.52  fof(f36,plain,(
% 1.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f19])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.21/0.52    inference(nnf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.21/0.52  fof(f49,plain,(
% 1.21/0.52    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(backward_demodulation,[],[f47,f48])).
% 1.21/0.52  fof(f48,plain,(
% 1.21/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.21/0.52    inference(resolution,[],[f25,f34])).
% 1.21/0.52  fof(f34,plain,(
% 1.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f14])).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,axiom,(
% 1.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.52    inference(flattening,[],[f15])).
% 1.21/0.52  fof(f15,plain,(
% 1.21/0.52    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.52    inference(nnf_transformation,[],[f12])).
% 1.21/0.52  fof(f12,plain,(
% 1.21/0.52    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f11])).
% 1.21/0.52  fof(f11,negated_conjecture,(
% 1.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.21/0.52    inference(negated_conjecture,[],[f10])).
% 1.21/0.52  fof(f10,conjecture,(
% 1.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.21/0.52  fof(f47,plain,(
% 1.21/0.52    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.52    inference(forward_demodulation,[],[f26,f29])).
% 1.21/0.52  fof(f29,plain,(
% 1.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,axiom,(
% 1.21/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  fof(f43,plain,(
% 1.21/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.21/0.52    inference(equality_resolution,[],[f39])).
% 1.21/0.52  fof(f39,plain,(
% 1.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f24])).
% 1.21/0.52  % (19292)Refutation not found, incomplete strategy% (19292)------------------------------
% 1.21/0.52  % (19292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (19303)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.52  % (19292)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (19292)Memory used [KB]: 1663
% 1.21/0.52  % (19292)Time elapsed: 0.110 s
% 1.21/0.52  % (19292)------------------------------
% 1.21/0.52  % (19292)------------------------------
% 1.21/0.52  fof(f207,plain,(
% 1.21/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,sK1) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(superposition,[],[f44,f193])).
% 1.21/0.52  fof(f193,plain,(
% 1.21/0.52    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(resolution,[],[f179,f36])).
% 1.21/0.52  fof(f179,plain,(
% 1.21/0.52    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(superposition,[],[f31,f120])).
% 1.21/0.52  fof(f120,plain,(
% 1.21/0.52    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,sK1) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(superposition,[],[f32,f52])).
% 1.21/0.52  fof(f52,plain,(
% 1.21/0.52    sK1 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(resolution,[],[f49,f33])).
% 1.21/0.52  fof(f33,plain,(
% 1.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  fof(f13,plain,(
% 1.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.21/0.52    inference(ennf_transformation,[],[f4])).
% 1.21/0.52  fof(f4,axiom,(
% 1.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.21/0.52  % (19319)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.21/0.52  fof(f32,plain,(
% 1.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f3])).
% 1.21/0.52  fof(f3,axiom,(
% 1.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f6])).
% 1.21/0.52  fof(f6,axiom,(
% 1.21/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.21/0.52  fof(f240,plain,(
% 1.21/0.52    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,sK1,X0),X0) | k1_xboole_0 = sK1 | k1_xboole_0 = X0) )),
% 1.21/0.52    inference(subsumption_resolution,[],[f228,f219])).
% 1.21/0.52  % (19294)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  fof(f219,plain,(
% 1.21/0.52    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f216])).
% 1.21/0.52  fof(f216,plain,(
% 1.21/0.52    ( ! [X8] : (k1_xboole_0 = sK1 | ~r2_hidden(X8,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(resolution,[],[f211,f99])).
% 1.21/0.52  fof(f99,plain,(
% 1.21/0.52    ( ! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.21/0.52    inference(superposition,[],[f45,f51])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.21/0.52    inference(equality_resolution,[],[f37])).
% 1.21/0.52  % (19302)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f24])).
% 1.21/0.52  fof(f228,plain,(
% 1.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK1 | r2_hidden(sK2(k1_xboole_0,sK1,X0),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,sK1,X0),X0)) )),
% 1.21/0.52    inference(superposition,[],[f210,f40])).
% 1.21/0.52  fof(f40,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f24])).
% 1.21/0.52  fof(f210,plain,(
% 1.21/0.52    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f197])).
% 1.21/0.52  fof(f197,plain,(
% 1.21/0.52    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.21/0.52    inference(superposition,[],[f193,f190])).
% 1.21/0.52  fof(f190,plain,(
% 1.21/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | k1_xboole_0 = sK1),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f171])).
% 1.21/0.52  fof(f171,plain,(
% 1.21/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.21/0.52    inference(superposition,[],[f120,f51])).
% 1.21/0.52  fof(f509,plain,(
% 1.21/0.52    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 1.21/0.52    inference(trivial_inequality_removal,[],[f481])).
% 1.21/0.52  fof(f481,plain,(
% 1.21/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 1.21/0.52    inference(backward_demodulation,[],[f50,f465])).
% 1.21/0.52  fof(f50,plain,(
% 1.21/0.52    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 != sK1),
% 1.21/0.52    inference(backward_demodulation,[],[f46,f48])).
% 1.21/0.52  fof(f46,plain,(
% 1.21/0.52    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.52    inference(forward_demodulation,[],[f27,f29])).
% 1.21/0.52  fof(f27,plain,(
% 1.21/0.52    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (19315)------------------------------
% 1.21/0.52  % (19315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (19315)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (19315)Memory used [KB]: 2046
% 1.21/0.52  % (19315)Time elapsed: 0.069 s
% 1.21/0.52  % (19315)------------------------------
% 1.21/0.52  % (19315)------------------------------
% 1.21/0.52  % (19298)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (19302)Refutation not found, incomplete strategy% (19302)------------------------------
% 1.21/0.52  % (19302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (19302)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (19302)Memory used [KB]: 10618
% 1.21/0.52  % (19302)Time elapsed: 0.120 s
% 1.21/0.52  % (19302)------------------------------
% 1.21/0.52  % (19302)------------------------------
% 1.21/0.52  % (19291)Success in time 0.17 s
%------------------------------------------------------------------------------
