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
% DateTime   : Thu Dec  3 12:29:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 263 expanded)
%              Number of leaves         :    6 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  143 (1761 expanded)
%              Number of equality atoms :   27 ( 286 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f149,f84])).

fof(f84,plain,(
    ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f62,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0)) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

fof(f12,plain,(
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

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f29,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),sK0)
    | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0)) ) ),
    inference(superposition,[],[f44,f15])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,sK0)) ) ),
    inference(resolution,[],[f33,f24])).

fof(f149,plain,(
    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f148,f29])).

fof(f148,plain,(
    ! [X0] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f147,f84])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f146,f89])).

fof(f89,plain,(
    ! [X2,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(sK0,X2))) ),
    inference(forward_demodulation,[],[f82,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f82,plain,(
    ! [X2,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,sK0),X2)) ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(sK0,sK1)))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ) ),
    inference(condensation,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(sK0,sK1)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1) ) ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k1_xboole_0))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X5,k2_xboole_0(sK0,sK1)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5) ) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),k2_xboole_0(sK0,sK1))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1861)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (1851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (1851)Refutation not found, incomplete strategy% (1851)------------------------------
% 0.20/0.46  % (1851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (1851)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (1851)Memory used [KB]: 6012
% 0.20/0.46  % (1851)Time elapsed: 0.003 s
% 0.20/0.46  % (1851)------------------------------
% 0.20/0.46  % (1851)------------------------------
% 0.20/0.46  % (1843)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (1861)Refutation not found, incomplete strategy% (1861)------------------------------
% 0.20/0.46  % (1861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (1861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (1861)Memory used [KB]: 10490
% 0.20/0.46  % (1861)Time elapsed: 0.056 s
% 0.20/0.46  % (1861)------------------------------
% 0.20/0.46  % (1861)------------------------------
% 0.20/0.47  % (1852)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (1852)Refutation not found, incomplete strategy% (1852)------------------------------
% 0.20/0.47  % (1852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1852)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (1852)Memory used [KB]: 1535
% 0.20/0.47  % (1852)Time elapsed: 0.072 s
% 0.20/0.47  % (1852)------------------------------
% 0.20/0.47  % (1852)------------------------------
% 0.20/0.48  % (1845)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (1846)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (1844)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (1857)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (1839)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (1854)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (1839)Refutation not found, incomplete strategy% (1839)------------------------------
% 0.20/0.49  % (1839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1839)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1839)Memory used [KB]: 10490
% 0.20/0.49  % (1839)Time elapsed: 0.080 s
% 0.20/0.49  % (1839)------------------------------
% 0.20/0.49  % (1839)------------------------------
% 0.20/0.49  % (1842)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (1842)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f149,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    inference(superposition,[],[f62,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f55,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0))) )),
% 0.20/0.49    inference(resolution,[],[f29,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),sK0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    inference(equality_resolution,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),X0)) )),
% 0.20/0.49    inference(superposition,[],[f14,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0))) )),
% 0.20/0.49    inference(superposition,[],[f44,f15])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,sK0))) )),
% 0.20/0.49    inference(resolution,[],[f33,f24])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f148,f29])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f147,f84])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f146,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(sK0,X2)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f82,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,sK0),X2))) )),
% 0.20/0.49    inference(resolution,[],[f62,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(sK0,sK1))) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.49    inference(condensation,[],[f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1)) )),
% 0.20/0.49    inference(resolution,[],[f51,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X4,X5] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k1_xboole_0)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X5,k2_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5)) )),
% 0.20/0.49    inference(resolution,[],[f36,f23])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.49    inference(resolution,[],[f30,f24])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(equality_resolution,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),k2_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),X1)) )),
% 0.20/0.49    inference(superposition,[],[f14,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (1842)------------------------------
% 0.20/0.49  % (1842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1842)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (1842)Memory used [KB]: 1663
% 0.20/0.49  % (1842)Time elapsed: 0.100 s
% 0.20/0.49  % (1842)------------------------------
% 0.20/0.49  % (1842)------------------------------
% 0.20/0.50  % (1832)Success in time 0.145 s
%------------------------------------------------------------------------------
