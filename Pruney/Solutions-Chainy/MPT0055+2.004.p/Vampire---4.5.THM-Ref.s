%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 2.94s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 362 expanded)
%              Number of leaves         :    7 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  151 (2401 expanded)
%              Number of equality atoms :   34 ( 414 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2281,plain,(
    $false ),
    inference(resolution,[],[f2237,f731])).

fof(f731,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f730,f386])).

fof(f386,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK1)) ) ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),k4_xboole_0(X1,sK1)) ) ),
    inference(resolution,[],[f108,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f108,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)
      | k3_xboole_0(sK0,sK1) != X1 ) ),
    inference(subsumption_resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f32,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f101,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK0) ) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | k3_xboole_0(sK0,sK1) != X1
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f730,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f724,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f724,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(factoring,[],[f252])).

fof(f252,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(sK0,sK1) != X3
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),X3)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),k4_xboole_0(sK0,X4))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),X4) ) ),
    inference(resolution,[],[f64,f57])).

fof(f2237,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0) ),
    inference(subsumption_resolution,[],[f2224,f1016])).

fof(f1016,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f1015,f731])).

fof(f1015,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1006,f32])).

fof(f1006,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f946,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f946,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f733,f41])).

fof(f733,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f731,f58])).

fof(f2224,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f2174,f57])).

fof(f2174,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f951,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f951,plain,(
    ! [X8,X7] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f733,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (1612)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (1604)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (1597)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (1612)Refutation not found, incomplete strategy% (1612)------------------------------
% 0.20/0.47  % (1612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (1612)Memory used [KB]: 6140
% 0.20/0.47  % (1612)Time elapsed: 0.065 s
% 0.20/0.47  % (1612)------------------------------
% 0.20/0.47  % (1612)------------------------------
% 0.20/0.47  % (1597)Refutation not found, incomplete strategy% (1597)------------------------------
% 0.20/0.47  % (1597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1597)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (1597)Memory used [KB]: 6140
% 0.20/0.47  % (1597)Time elapsed: 0.061 s
% 0.20/0.47  % (1597)------------------------------
% 0.20/0.47  % (1597)------------------------------
% 0.20/0.48  % (1599)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (1598)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (1615)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (1598)Refutation not found, incomplete strategy% (1598)------------------------------
% 0.20/0.48  % (1598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1598)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1598)Memory used [KB]: 10618
% 0.20/0.48  % (1598)Time elapsed: 0.071 s
% 0.20/0.48  % (1598)------------------------------
% 0.20/0.48  % (1598)------------------------------
% 0.20/0.48  % (1607)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (1600)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (1607)Refutation not found, incomplete strategy% (1607)------------------------------
% 0.20/0.48  % (1607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1607)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1607)Memory used [KB]: 6012
% 0.20/0.48  % (1607)Time elapsed: 0.077 s
% 0.20/0.48  % (1607)------------------------------
% 0.20/0.48  % (1607)------------------------------
% 0.20/0.48  % (1600)Refutation not found, incomplete strategy% (1600)------------------------------
% 0.20/0.48  % (1600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1600)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1600)Memory used [KB]: 10618
% 0.20/0.48  % (1600)Time elapsed: 0.070 s
% 0.20/0.48  % (1600)------------------------------
% 0.20/0.48  % (1600)------------------------------
% 0.20/0.49  % (1613)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (1616)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (1602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (1610)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (1610)Refutation not found, incomplete strategy% (1610)------------------------------
% 0.20/0.49  % (1610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1610)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1610)Memory used [KB]: 1663
% 0.20/0.49  % (1610)Time elapsed: 0.081 s
% 0.20/0.49  % (1610)------------------------------
% 0.20/0.49  % (1610)------------------------------
% 0.20/0.49  % (1614)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (1606)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (1608)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (1608)Refutation not found, incomplete strategy% (1608)------------------------------
% 0.20/0.49  % (1608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1608)Memory used [KB]: 10618
% 0.20/0.49  % (1608)Time elapsed: 0.083 s
% 0.20/0.49  % (1608)------------------------------
% 0.20/0.49  % (1608)------------------------------
% 0.20/0.50  % (1601)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (1617)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (1617)Refutation not found, incomplete strategy% (1617)------------------------------
% 0.20/0.50  % (1617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1617)Memory used [KB]: 10490
% 0.20/0.50  % (1617)Time elapsed: 0.084 s
% 0.20/0.50  % (1617)------------------------------
% 0.20/0.50  % (1617)------------------------------
% 0.20/0.50  % (1611)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (1609)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1609)Refutation not found, incomplete strategy% (1609)------------------------------
% 0.20/0.50  % (1609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1609)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1609)Memory used [KB]: 6012
% 0.20/0.50  % (1609)Time elapsed: 0.002 s
% 0.20/0.50  % (1609)------------------------------
% 0.20/0.50  % (1609)------------------------------
% 0.20/0.51  % (1605)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (1603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 2.94/0.73  % (1601)Refutation found. Thanks to Tanya!
% 2.94/0.73  % SZS status Theorem for theBenchmark
% 2.94/0.73  % SZS output start Proof for theBenchmark
% 2.94/0.73  fof(f2281,plain,(
% 2.94/0.73    $false),
% 2.94/0.73    inference(resolution,[],[f2237,f731])).
% 2.94/0.73  fof(f731,plain,(
% 2.94/0.73    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.94/0.73    inference(subsumption_resolution,[],[f730,f386])).
% 2.94/0.73  fof(f386,plain,(
% 2.94/0.73    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK1))) )),
% 2.94/0.73    inference(equality_resolution,[],[f160])).
% 2.94/0.73  fof(f160,plain,(
% 2.94/0.73    ( ! [X0,X1] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),k4_xboole_0(X1,sK1))) )),
% 2.94/0.73    inference(resolution,[],[f108,f58])).
% 2.94/0.73  fof(f58,plain,(
% 2.94/0.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.94/0.73    inference(equality_resolution,[],[f52])).
% 2.94/0.73  fof(f52,plain,(
% 2.94/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.94/0.73    inference(cnf_transformation,[],[f31])).
% 2.94/0.73  fof(f31,plain,(
% 2.94/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.94/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 2.94/0.73  fof(f30,plain,(
% 2.94/0.73    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.94/0.73    introduced(choice_axiom,[])).
% 2.94/0.73  fof(f29,plain,(
% 2.94/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.94/0.73    inference(rectify,[],[f28])).
% 2.94/0.73  fof(f28,plain,(
% 2.94/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.94/0.73    inference(flattening,[],[f27])).
% 2.94/0.73  fof(f27,plain,(
% 2.94/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.94/0.73    inference(nnf_transformation,[],[f3])).
% 2.94/0.73  fof(f3,axiom,(
% 2.94/0.73    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.94/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.94/0.73  fof(f108,plain,(
% 2.94/0.73    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) | k3_xboole_0(sK0,sK1) != X1) )),
% 2.94/0.73    inference(subsumption_resolution,[],[f101,f64])).
% 2.94/0.73  fof(f64,plain,(
% 2.94/0.73    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.94/0.73    inference(superposition,[],[f32,f54])).
% 2.94/0.73  fof(f54,plain,(
% 2.94/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.94/0.73    inference(cnf_transformation,[],[f31])).
% 2.94/0.73  fof(f32,plain,(
% 2.94/0.73    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.94/0.73    inference(cnf_transformation,[],[f22])).
% 2.94/0.73  fof(f22,plain,(
% 2.94/0.73    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.94/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 2.94/0.73  fof(f21,plain,(
% 2.94/0.73    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.94/0.73    introduced(choice_axiom,[])).
% 2.94/0.75  fof(f19,plain,(
% 2.94/0.75    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.94/0.75    inference(ennf_transformation,[],[f17])).
% 2.94/0.75  fof(f17,negated_conjecture,(
% 2.94/0.75    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.94/0.75    inference(negated_conjecture,[],[f16])).
% 2.94/0.75  fof(f16,conjecture,(
% 2.94/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.94/0.75  fof(f101,plain,(
% 2.94/0.75    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK0)) )),
% 2.94/0.75    inference(resolution,[],[f65,f57])).
% 2.94/0.75  fof(f57,plain,(
% 2.94/0.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.94/0.75    inference(equality_resolution,[],[f53])).
% 2.94/0.75  fof(f53,plain,(
% 2.94/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.94/0.75    inference(cnf_transformation,[],[f31])).
% 2.94/0.75  fof(f65,plain,(
% 2.94/0.75    ( ! [X1] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | k3_xboole_0(sK0,sK1) != X1 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.94/0.75    inference(superposition,[],[f32,f55])).
% 2.94/0.75  fof(f55,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f31])).
% 2.94/0.75  fof(f730,plain,(
% 2.94/0.75    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.94/0.75    inference(forward_demodulation,[],[f724,f41])).
% 2.94/0.75  fof(f41,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f15])).
% 2.94/0.75  fof(f15,axiom,(
% 2.94/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.94/0.75  fof(f724,plain,(
% 2.94/0.75    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 2.94/0.75    inference(factoring,[],[f252])).
% 2.94/0.75  fof(f252,plain,(
% 2.94/0.75    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0)) )),
% 2.94/0.75    inference(equality_resolution,[],[f90])).
% 2.94/0.75  fof(f90,plain,(
% 2.94/0.75    ( ! [X4,X3] : (k3_xboole_0(sK0,sK1) != X3 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),X3) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),k4_xboole_0(sK0,X4)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X3),X4)) )),
% 2.94/0.75    inference(resolution,[],[f64,f57])).
% 2.94/0.75  fof(f2237,plain,(
% 2.94/0.75    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f2224,f1016])).
% 2.94/0.75  fof(f1016,plain,(
% 2.94/0.75    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f1015,f731])).
% 2.94/0.75  fof(f1015,plain,(
% 2.94/0.75    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.94/0.75    inference(subsumption_resolution,[],[f1006,f32])).
% 2.94/0.75  fof(f1006,plain,(
% 2.94/0.75    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.94/0.75    inference(resolution,[],[f946,f56])).
% 2.94/0.75  fof(f56,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f31])).
% 2.94/0.75  fof(f946,plain,(
% 2.94/0.75    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.94/0.75    inference(superposition,[],[f733,f41])).
% 2.94/0.75  fof(f733,plain,(
% 2.94/0.75    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 2.94/0.75    inference(resolution,[],[f731,f58])).
% 2.94/0.75  fof(f2224,plain,(
% 2.94/0.75    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X0)) )),
% 2.94/0.75    inference(resolution,[],[f2174,f57])).
% 2.94/0.75  fof(f2174,plain,(
% 2.94/0.75    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0))) )),
% 2.94/0.75    inference(superposition,[],[f951,f39])).
% 2.94/0.75  fof(f39,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.94/0.75    inference(cnf_transformation,[],[f10])).
% 2.94/0.75  fof(f10,axiom,(
% 2.94/0.75    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.94/0.75  fof(f951,plain,(
% 2.94/0.75    ( ! [X8,X7] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))) )),
% 2.94/0.75    inference(superposition,[],[f733,f50])).
% 2.94/0.75  fof(f50,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f14])).
% 2.94/0.75  fof(f14,axiom,(
% 2.94/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.94/0.75  % SZS output end Proof for theBenchmark
% 2.94/0.75  % (1601)------------------------------
% 2.94/0.75  % (1601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.75  % (1601)Termination reason: Refutation
% 2.94/0.75  
% 2.94/0.75  % (1601)Memory used [KB]: 3454
% 2.94/0.75  % (1601)Time elapsed: 0.318 s
% 2.94/0.75  % (1601)------------------------------
% 2.94/0.75  % (1601)------------------------------
% 2.94/0.75  % (1596)Success in time 0.396 s
%------------------------------------------------------------------------------
