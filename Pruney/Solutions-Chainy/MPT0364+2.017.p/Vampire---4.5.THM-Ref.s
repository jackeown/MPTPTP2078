%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:13 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 295 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  248 (1180 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1078,f100])).

fof(f100,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f98,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

% (32081)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (32076)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (32087)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (32090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (32079)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (32073)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f98,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f96,f97])).

fof(f97,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f95,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f95,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f60,f94])).

fof(f94,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f60,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f61,f94])).

fof(f61,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1078,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1077,f147])).

fof(f147,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f131,f144])).

fof(f144,plain,(
    ! [X9] : k2_xboole_0(k1_xboole_0,X9) = X9 ),
    inference(resolution,[],[f117,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f117,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(resolution,[],[f110,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f110,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f108,f104])).

fof(f104,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f97,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f108,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f114,plain,(
    ! [X5] : r1_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1077,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f208,f1072])).

fof(f1072,plain,(
    ! [X9] : sK0 = k2_xboole_0(k4_xboole_0(sK1,X9),sK0) ),
    inference(resolution,[],[f1063,f71])).

fof(f1063,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK1,X5),sK0) ),
    inference(resolution,[],[f960,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f960,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f955,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f955,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f947])).

fof(f947,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f268,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f268,plain,(
    ! [X8] :
      ( r2_hidden(sK7(sK1,X8),sK0)
      | r1_tarski(sK1,X8) ) ),
    inference(resolution,[],[f91,f81])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f208,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),sK0),sK0) ),
    inference(resolution,[],[f195,f73])).

fof(f195,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f103,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f97,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (32078)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (32094)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (32072)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.55  % (32086)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.56  % (32075)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.65/0.56  % (32093)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.65/0.56  % (32085)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.65/0.57  % (32091)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.65/0.57  % (32083)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.65/0.57  % (32082)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.65/0.58  % (32077)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.65/0.58  % (32088)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.65/0.58  % (32080)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.65/0.58  % (32071)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.65/0.58  % (32099)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.65/0.59  % (32096)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.65/0.59  % (32074)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.65/0.59  % (32082)Refutation not found, incomplete strategy% (32082)------------------------------
% 1.65/0.59  % (32082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (32082)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (32082)Memory used [KB]: 10618
% 1.65/0.59  % (32082)Time elapsed: 0.171 s
% 1.65/0.59  % (32082)------------------------------
% 1.65/0.59  % (32082)------------------------------
% 1.65/0.59  % (32094)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f1079,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(subsumption_resolution,[],[f1078,f100])).
% 1.65/0.59  fof(f100,plain,(
% 1.65/0.59    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.65/0.59    inference(resolution,[],[f98,f85])).
% 1.65/0.59  fof(f85,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f57])).
% 1.65/0.59  fof(f57,plain,(
% 1.65/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.65/0.59    inference(nnf_transformation,[],[f6])).
% 1.65/0.60  % (32081)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.60  % (32076)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.65/0.60  % (32087)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.61  % (32090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.65/0.61  % (32079)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.62  % (32073)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.65/0.62  fof(f6,axiom,(
% 1.65/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.65/0.62  fof(f98,plain,(
% 1.65/0.62    ~r1_tarski(sK1,sK2)),
% 1.65/0.62    inference(subsumption_resolution,[],[f96,f97])).
% 1.65/0.62  fof(f97,plain,(
% 1.65/0.62    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.65/0.62    inference(subsumption_resolution,[],[f95,f87])).
% 1.65/0.62  fof(f87,plain,(
% 1.65/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f35])).
% 1.65/0.62  fof(f35,plain,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.65/0.62    inference(ennf_transformation,[],[f13])).
% 1.65/0.62  fof(f13,axiom,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.65/0.62  fof(f95,plain,(
% 1.65/0.62    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | r1_tarski(sK1,sK2)),
% 1.65/0.62    inference(backward_demodulation,[],[f60,f94])).
% 1.65/0.62  fof(f94,plain,(
% 1.65/0.62    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.65/0.62    inference(resolution,[],[f59,f74])).
% 1.65/0.62  fof(f74,plain,(
% 1.65/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.62    inference(cnf_transformation,[],[f30])).
% 1.65/0.62  fof(f30,plain,(
% 1.65/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.62    inference(ennf_transformation,[],[f17])).
% 1.65/0.62  fof(f17,axiom,(
% 1.65/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.62  fof(f59,plain,(
% 1.65/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.62    inference(cnf_transformation,[],[f43])).
% 1.65/0.62  fof(f43,plain,(
% 1.65/0.62    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).
% 1.65/0.62  fof(f41,plain,(
% 1.65/0.62    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.65/0.62    introduced(choice_axiom,[])).
% 1.65/0.62  fof(f42,plain,(
% 1.65/0.62    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.65/0.62    introduced(choice_axiom,[])).
% 1.65/0.62  fof(f40,plain,(
% 1.65/0.62    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.62    inference(flattening,[],[f39])).
% 1.65/0.62  fof(f39,plain,(
% 1.65/0.62    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.62    inference(nnf_transformation,[],[f23])).
% 1.65/0.62  fof(f23,plain,(
% 1.65/0.62    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.62    inference(ennf_transformation,[],[f20])).
% 1.65/0.62  fof(f20,negated_conjecture,(
% 1.65/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.65/0.62    inference(negated_conjecture,[],[f19])).
% 1.65/0.62  fof(f19,conjecture,(
% 1.65/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 1.65/0.62  fof(f60,plain,(
% 1.65/0.62    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.65/0.62    inference(cnf_transformation,[],[f43])).
% 1.65/0.62  fof(f96,plain,(
% 1.65/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~r1_tarski(sK1,sK2)),
% 1.65/0.62    inference(backward_demodulation,[],[f61,f94])).
% 1.65/0.62  fof(f61,plain,(
% 1.65/0.62    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.65/0.62    inference(cnf_transformation,[],[f43])).
% 1.65/0.62  fof(f1078,plain,(
% 1.65/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.65/0.62    inference(forward_demodulation,[],[f1077,f147])).
% 1.65/0.62  fof(f147,plain,(
% 1.65/0.62    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.65/0.62    inference(backward_demodulation,[],[f131,f144])).
% 1.65/0.62  fof(f144,plain,(
% 1.65/0.62    ( ! [X9] : (k2_xboole_0(k1_xboole_0,X9) = X9) )),
% 1.65/0.62    inference(resolution,[],[f117,f71])).
% 1.65/0.62  fof(f71,plain,(
% 1.65/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f27])).
% 1.65/0.62  fof(f27,plain,(
% 1.65/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.65/0.62    inference(ennf_transformation,[],[f7])).
% 1.65/0.62  fof(f7,axiom,(
% 1.65/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.65/0.62  fof(f117,plain,(
% 1.65/0.62    ( ! [X8] : (r1_tarski(k1_xboole_0,X8)) )),
% 1.65/0.62    inference(resolution,[],[f110,f81])).
% 1.65/0.62  fof(f81,plain,(
% 1.65/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f55])).
% 1.65/0.62  fof(f55,plain,(
% 1.65/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).
% 1.65/0.62  fof(f54,plain,(
% 1.65/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.65/0.62    introduced(choice_axiom,[])).
% 1.65/0.62  fof(f53,plain,(
% 1.65/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.62    inference(rectify,[],[f52])).
% 1.65/0.62  fof(f52,plain,(
% 1.65/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.62    inference(nnf_transformation,[],[f34])).
% 1.65/0.62  fof(f34,plain,(
% 1.65/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.65/0.62    inference(ennf_transformation,[],[f1])).
% 1.65/0.62  fof(f1,axiom,(
% 1.65/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.65/0.62  fof(f110,plain,(
% 1.65/0.62    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.65/0.62    inference(forward_demodulation,[],[f108,f104])).
% 1.65/0.62  fof(f104,plain,(
% 1.65/0.62    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.65/0.62    inference(resolution,[],[f97,f83])).
% 1.65/0.62  fof(f83,plain,(
% 1.65/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f56])).
% 1.65/0.62  fof(f56,plain,(
% 1.65/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(nnf_transformation,[],[f2])).
% 1.65/0.62  fof(f2,axiom,(
% 1.65/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.62  fof(f108,plain,(
% 1.65/0.62    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) )),
% 1.65/0.62    inference(resolution,[],[f97,f67])).
% 1.65/0.62  fof(f67,plain,(
% 1.65/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.65/0.62    inference(cnf_transformation,[],[f45])).
% 1.65/0.62  fof(f45,plain,(
% 1.65/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f44])).
% 1.65/0.62  fof(f44,plain,(
% 1.65/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.65/0.62    introduced(choice_axiom,[])).
% 1.65/0.62  fof(f25,plain,(
% 1.65/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(ennf_transformation,[],[f21])).
% 1.65/0.62  fof(f21,plain,(
% 1.65/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(rectify,[],[f5])).
% 1.65/0.62  fof(f5,axiom,(
% 1.65/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.65/0.62  fof(f131,plain,(
% 1.65/0.62    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)) )),
% 1.65/0.62    inference(resolution,[],[f114,f73])).
% 1.65/0.62  fof(f73,plain,(
% 1.65/0.62    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f29])).
% 1.65/0.62  fof(f29,plain,(
% 1.65/0.62    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.65/0.62    inference(ennf_transformation,[],[f14])).
% 1.65/0.62  fof(f14,axiom,(
% 1.65/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.65/0.62  fof(f114,plain,(
% 1.65/0.62    ( ! [X5] : (r1_xboole_0(k1_xboole_0,X5)) )),
% 1.65/0.62    inference(resolution,[],[f110,f68])).
% 1.65/0.62  fof(f68,plain,(
% 1.65/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f47])).
% 1.65/0.62  fof(f47,plain,(
% 1.65/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f46])).
% 1.65/0.62  fof(f46,plain,(
% 1.65/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.65/0.62    introduced(choice_axiom,[])).
% 1.65/0.62  fof(f26,plain,(
% 1.65/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(ennf_transformation,[],[f22])).
% 1.65/0.62  fof(f22,plain,(
% 1.65/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.62    inference(rectify,[],[f4])).
% 1.65/0.62  fof(f4,axiom,(
% 1.65/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.65/0.62  fof(f1077,plain,(
% 1.65/0.62    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK0,sK0)),
% 1.65/0.62    inference(backward_demodulation,[],[f208,f1072])).
% 1.65/0.62  fof(f1072,plain,(
% 1.65/0.62    ( ! [X9] : (sK0 = k2_xboole_0(k4_xboole_0(sK1,X9),sK0)) )),
% 1.65/0.62    inference(resolution,[],[f1063,f71])).
% 1.65/0.62  fof(f1063,plain,(
% 1.65/0.62    ( ! [X5] : (r1_tarski(k4_xboole_0(sK1,X5),sK0)) )),
% 1.65/0.62    inference(resolution,[],[f960,f64])).
% 1.65/0.62  fof(f64,plain,(
% 1.65/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f9])).
% 1.65/0.62  fof(f9,axiom,(
% 1.65/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.65/0.62  fof(f960,plain,(
% 1.65/0.62    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,sK0)) )),
% 1.65/0.62    inference(resolution,[],[f955,f89])).
% 1.65/0.62  fof(f89,plain,(
% 1.65/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f38])).
% 1.65/0.62  fof(f38,plain,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.62    inference(flattening,[],[f37])).
% 1.65/0.62  fof(f37,plain,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.62    inference(ennf_transformation,[],[f8])).
% 1.65/0.62  fof(f8,axiom,(
% 1.65/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.65/0.62  fof(f955,plain,(
% 1.65/0.62    r1_tarski(sK1,sK0)),
% 1.65/0.62    inference(duplicate_literal_removal,[],[f947])).
% 1.65/0.62  fof(f947,plain,(
% 1.65/0.62    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.65/0.62    inference(resolution,[],[f268,f82])).
% 1.65/0.62  fof(f82,plain,(
% 1.65/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f55])).
% 1.65/0.62  fof(f268,plain,(
% 1.65/0.62    ( ! [X8] : (r2_hidden(sK7(sK1,X8),sK0) | r1_tarski(sK1,X8)) )),
% 1.65/0.62    inference(resolution,[],[f91,f81])).
% 1.65/0.62  fof(f91,plain,(
% 1.65/0.62    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.65/0.62    inference(resolution,[],[f58,f75])).
% 1.65/0.62  fof(f75,plain,(
% 1.65/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.62    inference(cnf_transformation,[],[f31])).
% 1.65/0.62  fof(f31,plain,(
% 1.65/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.62    inference(ennf_transformation,[],[f18])).
% 1.65/0.62  fof(f18,axiom,(
% 1.65/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.65/0.62  fof(f58,plain,(
% 1.65/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.62    inference(cnf_transformation,[],[f43])).
% 1.65/0.62  fof(f208,plain,(
% 1.65/0.62    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),sK0),sK0)),
% 1.65/0.62    inference(resolution,[],[f195,f73])).
% 1.65/0.62  fof(f195,plain,(
% 1.65/0.62    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.65/0.62    inference(resolution,[],[f103,f72])).
% 1.65/0.62  fof(f72,plain,(
% 1.65/0.62    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.62    inference(cnf_transformation,[],[f28])).
% 1.65/0.62  fof(f28,plain,(
% 1.65/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.65/0.62    inference(ennf_transformation,[],[f3])).
% 1.65/0.62  fof(f3,axiom,(
% 1.65/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.65/0.62  fof(f103,plain,(
% 1.65/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.65/0.62    inference(resolution,[],[f97,f88])).
% 1.65/0.62  fof(f88,plain,(
% 1.65/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 1.65/0.62    inference(cnf_transformation,[],[f36])).
% 1.65/0.62  fof(f36,plain,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.65/0.62    inference(ennf_transformation,[],[f12])).
% 1.65/0.62  fof(f12,axiom,(
% 1.65/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.65/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.65/0.62  % SZS output end Proof for theBenchmark
% 1.65/0.62  % (32094)------------------------------
% 1.65/0.62  % (32094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.62  % (32094)Termination reason: Refutation
% 1.65/0.62  
% 1.65/0.62  % (32094)Memory used [KB]: 2174
% 1.65/0.62  % (32094)Time elapsed: 0.165 s
% 1.65/0.62  % (32094)------------------------------
% 1.65/0.62  % (32094)------------------------------
% 1.65/0.62  % (32070)Success in time 0.262 s
%------------------------------------------------------------------------------
