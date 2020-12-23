%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:54 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 188 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 ( 516 expanded)
%              Number of equality atoms :   57 ( 157 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f289,f283])).

fof(f283,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f280,f276])).

fof(f276,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f275,f175])).

fof(f175,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f174,f61])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f38,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f174,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f164,f38])).

fof(f164,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f51,f161])).

fof(f161,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f76,f72])).

fof(f72,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f71,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f71,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

% (20741)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f275,plain,(
    k2_xboole_0(sK0,sK1) = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f267,f38])).

fof(f267,plain,(
    k2_xboole_0(sK1,sK0) = k4_subset_1(sK0,sK1,sK0) ),
    inference(resolution,[],[f266,f114])).

fof(f114,plain,(
    ! [X3] : r2_hidden(X3,k1_zfmisc_1(X3)) ),
    inference(superposition,[],[f69,f109])).

fof(f109,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f106,f61])).

fof(f106,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f51,f61])).

fof(f69,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f266,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f264,f50])).

fof(f264,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f260,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f280,plain,(
    k2_xboole_0(sK1,sK0) = k4_subset_1(sK0,sK1,sK0) ),
    inference(superposition,[],[f268,f109])).

fof(f268,plain,(
    ! [X0] : k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f266,f69])).

fof(f289,plain,(
    sK0 != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f282,f51])).

fof(f282,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f203,f268])).

fof(f203,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f60,f201])).

fof(f201,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f60,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.52  % (20736)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.53  % (20732)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (20721)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.53  % (20736)Refutation not found, incomplete strategy% (20736)------------------------------
% 1.22/0.53  % (20736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (20736)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (20736)Memory used [KB]: 6140
% 1.22/0.53  % (20736)Time elapsed: 0.004 s
% 1.22/0.53  % (20736)------------------------------
% 1.22/0.53  % (20736)------------------------------
% 1.22/0.53  % (20732)Refutation not found, incomplete strategy% (20732)------------------------------
% 1.22/0.53  % (20732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (20728)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.53  % (20738)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.53  % (20720)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (20727)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.53  % (20724)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.53  % (20726)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.53  % (20720)Refutation not found, incomplete strategy% (20720)------------------------------
% 1.22/0.53  % (20720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (20747)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.53  % (20725)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (20720)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20720)Memory used [KB]: 1663
% 1.35/0.54  % (20720)Time elapsed: 0.112 s
% 1.35/0.54  % (20720)------------------------------
% 1.35/0.54  % (20720)------------------------------
% 1.35/0.54  % (20738)Refutation not found, incomplete strategy% (20738)------------------------------
% 1.35/0.54  % (20738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (20738)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20738)Memory used [KB]: 10618
% 1.35/0.54  % (20738)Time elapsed: 0.119 s
% 1.35/0.54  % (20738)------------------------------
% 1.35/0.54  % (20738)------------------------------
% 1.35/0.54  % (20737)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (20732)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20732)Memory used [KB]: 10618
% 1.35/0.54  % (20732)Time elapsed: 0.104 s
% 1.35/0.54  % (20732)------------------------------
% 1.35/0.54  % (20732)------------------------------
% 1.35/0.54  % (20730)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (20730)Refutation not found, incomplete strategy% (20730)------------------------------
% 1.35/0.54  % (20730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (20751)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (20726)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % (20744)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (20750)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (20725)Refutation not found, incomplete strategy% (20725)------------------------------
% 1.35/0.54  % (20725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (20725)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20725)Memory used [KB]: 6268
% 1.35/0.54  % (20725)Time elapsed: 0.125 s
% 1.35/0.54  % (20725)------------------------------
% 1.35/0.54  % (20725)------------------------------
% 1.35/0.54  % (20723)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (20723)Refutation not found, incomplete strategy% (20723)------------------------------
% 1.35/0.54  % (20723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (20723)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20723)Memory used [KB]: 10746
% 1.35/0.54  % (20723)Time elapsed: 0.121 s
% 1.35/0.54  % (20723)------------------------------
% 1.35/0.54  % (20723)------------------------------
% 1.35/0.55  % (20730)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (20730)Memory used [KB]: 10618
% 1.35/0.55  % (20730)Time elapsed: 0.131 s
% 1.35/0.55  % (20730)------------------------------
% 1.35/0.55  % (20730)------------------------------
% 1.35/0.55  % (20749)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (20729)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (20743)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.55  % (20739)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (20734)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (20745)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (20742)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f290,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(subsumption_resolution,[],[f289,f283])).
% 1.35/0.55  fof(f283,plain,(
% 1.35/0.55    sK0 = k2_xboole_0(sK1,sK0)),
% 1.35/0.55    inference(forward_demodulation,[],[f280,f276])).
% 1.35/0.55  fof(f276,plain,(
% 1.35/0.55    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.55    inference(forward_demodulation,[],[f275,f175])).
% 1.35/0.55  fof(f175,plain,(
% 1.35/0.55    sK0 = k2_xboole_0(sK0,sK1)),
% 1.35/0.55    inference(forward_demodulation,[],[f174,f61])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.35/0.55    inference(superposition,[],[f38,f52])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.55  fof(f38,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.35/0.55  fof(f174,plain,(
% 1.35/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0)),
% 1.35/0.55    inference(forward_demodulation,[],[f164,f38])).
% 1.35/0.55  fof(f164,plain,(
% 1.35/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.35/0.55    inference(superposition,[],[f51,f161])).
% 1.35/0.55  fof(f161,plain,(
% 1.35/0.55    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.35/0.55    inference(resolution,[],[f76,f72])).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(subsumption_resolution,[],[f71,f50])).
% 1.35/0.55  fof(f50,plain,(
% 1.35/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f15])).
% 1.35/0.55  fof(f15,axiom,(
% 1.35/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.35/0.55  fof(f71,plain,(
% 1.35/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(resolution,[],[f42,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.35/0.55    inference(negated_conjecture,[],[f17])).
% 1.35/0.55  fof(f17,conjecture,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(nnf_transformation,[],[f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,axiom,(
% 1.35/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.35/0.55  fof(f76,plain,(
% 1.35/0.55    ( ! [X2,X3] : (~r2_hidden(X2,k1_zfmisc_1(X3)) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 1.35/0.55    inference(resolution,[],[f54,f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(equality_resolution,[],[f46])).
% 1.35/0.55  fof(f46,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(rectify,[],[f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.35/0.55    inference(nnf_transformation,[],[f3])).
% 1.35/0.55  % (20741)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.35/0.55  fof(f51,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.35/0.55  fof(f275,plain,(
% 1.35/0.55    k2_xboole_0(sK0,sK1) = k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.55    inference(forward_demodulation,[],[f267,f38])).
% 1.35/0.55  fof(f267,plain,(
% 1.35/0.55    k2_xboole_0(sK1,sK0) = k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.55    inference(resolution,[],[f266,f114])).
% 1.35/0.55  fof(f114,plain,(
% 1.35/0.55    ( ! [X3] : (r2_hidden(X3,k1_zfmisc_1(X3))) )),
% 1.35/0.55    inference(superposition,[],[f69,f109])).
% 1.35/0.55  fof(f109,plain,(
% 1.35/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.35/0.55    inference(forward_demodulation,[],[f106,f61])).
% 1.35/0.55  fof(f106,plain,(
% 1.35/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.35/0.55    inference(superposition,[],[f51,f61])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(resolution,[],[f58,f55])).
% 1.35/0.55  fof(f55,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.35/0.55  fof(f58,plain,(
% 1.35/0.55    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(equality_resolution,[],[f47])).
% 1.35/0.55  fof(f47,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f30])).
% 1.35/0.55  fof(f266,plain,(
% 1.35/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f264,f50])).
% 1.35/0.55  fof(f264,plain,(
% 1.35/0.55    ( ! [X0] : (k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 1.35/0.55    inference(resolution,[],[f260,f43])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f26])).
% 1.35/0.55  fof(f260,plain,(
% 1.35/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 1.35/0.55    inference(resolution,[],[f39,f36])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(flattening,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.35/0.55    inference(ennf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.35/0.55  fof(f280,plain,(
% 1.35/0.55    k2_xboole_0(sK1,sK0) = k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.55    inference(superposition,[],[f268,f109])).
% 1.35/0.55  fof(f268,plain,(
% 1.35/0.55    ( ! [X0] : (k4_subset_1(sK0,sK1,k4_xboole_0(sK0,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK0,X0))) )),
% 1.35/0.55    inference(resolution,[],[f266,f69])).
% 1.35/0.55  fof(f289,plain,(
% 1.35/0.55    sK0 != k2_xboole_0(sK1,sK0)),
% 1.35/0.55    inference(superposition,[],[f282,f51])).
% 1.35/0.55  fof(f282,plain,(
% 1.35/0.55    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.35/0.55    inference(superposition,[],[f203,f268])).
% 1.35/0.55  fof(f203,plain,(
% 1.35/0.55    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.35/0.55    inference(backward_demodulation,[],[f60,f201])).
% 1.35/0.55  fof(f201,plain,(
% 1.35/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.35/0.55    inference(resolution,[],[f40,f36])).
% 1.35/0.55  fof(f40,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f14])).
% 1.35/0.56  fof(f14,axiom,(
% 1.35/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.35/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.35/0.56  fof(f60,plain,(
% 1.35/0.56    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.35/0.56    inference(backward_demodulation,[],[f37,f41])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f13])).
% 1.35/0.56  fof(f13,axiom,(
% 1.35/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.56  fof(f37,plain,(
% 1.35/0.56    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.35/0.56    inference(cnf_transformation,[],[f25])).
% 1.35/0.56  % SZS output end Proof for theBenchmark
% 1.35/0.56  % (20726)------------------------------
% 1.35/0.56  % (20726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (20726)Termination reason: Refutation
% 1.35/0.56  
% 1.35/0.56  % (20726)Memory used [KB]: 6396
% 1.35/0.56  % (20731)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.56  % (20726)Time elapsed: 0.128 s
% 1.35/0.56  % (20726)------------------------------
% 1.35/0.56  % (20726)------------------------------
% 1.35/0.56  % (20742)Refutation not found, incomplete strategy% (20742)------------------------------
% 1.35/0.56  % (20742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (20742)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (20742)Memory used [KB]: 1791
% 1.35/0.56  % (20742)Time elapsed: 0.137 s
% 1.35/0.56  % (20742)------------------------------
% 1.35/0.56  % (20742)------------------------------
% 1.35/0.56  % (20717)Success in time 0.189 s
%------------------------------------------------------------------------------
