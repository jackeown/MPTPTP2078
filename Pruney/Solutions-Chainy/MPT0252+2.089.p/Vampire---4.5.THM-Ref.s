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
% DateTime   : Thu Dec  3 12:39:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 124 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 409 expanded)
%              Number of equality atoms :   93 ( 212 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(resolution,[],[f138,f119])).

fof(f119,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f115,f82])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f115,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f83,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f138,plain,(
    ! [X0] : ~ r2_hidden(k2_tarski(sK1,X0),k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(resolution,[],[f135,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

% (1041)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f135,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(sK1,X0),k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3))) ),
    inference(resolution,[],[f126,f74])).

fof(f74,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK1,sK3)
    & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f126,plain,(
    ! [X19,X18] :
      ( ~ r1_tarski(X18,sK3)
      | ~ r1_tarski(k2_tarski(sK1,X19),X18) ) ),
    inference(resolution,[],[f119,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X0,sK3)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f87,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (1040)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (1050)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (1059)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (1070)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (1051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (1059)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (1070)Refutation not found, incomplete strategy% (1070)------------------------------
% 0.20/0.53  % (1070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1073)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (1070)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1070)Memory used [KB]: 1663
% 0.20/0.53  % (1070)Time elapsed: 0.070 s
% 0.20/0.53  % (1070)------------------------------
% 0.20/0.53  % (1070)------------------------------
% 0.20/0.54  % (1078)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (1065)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(resolution,[],[f138,f119])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(resolution,[],[f115,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.20/0.54    inference(equality_resolution,[],[f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.54    inference(rectify,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.54    inference(nnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(superposition,[],[f83,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f43,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f52,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f54,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f65,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 0.20/0.54    inference(equality_resolution,[],[f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.54    inference(definition_unfolding,[],[f63,f71])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.54    inference(nnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.20/0.54    inference(definition_folding,[],[f22,f23])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(k2_tarski(sK1,X0),k2_tarski(k2_tarski(sK1,sK2),sK3))) )),
% 0.20/0.54    inference(resolution,[],[f135,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  % (1041)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k2_tarski(sK1,X0),k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)))) )),
% 0.20/0.54    inference(resolution,[],[f126,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)),sK3)),
% 0.20/0.54    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ~r2_hidden(sK1,sK3) & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK1,sK3) & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X19,X18] : (~r1_tarski(X18,sK3) | ~r1_tarski(k2_tarski(sK1,X19),X18)) )),
% 0.20/0.54    inference(resolution,[],[f119,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X0,sK3) | ~r1_tarski(X1,X0)) )),
% 0.20/0.54    inference(resolution,[],[f87,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_tarski(X0,sK3)) )),
% 0.20/0.54    inference(resolution,[],[f48,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ~r2_hidden(sK1,sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (1059)------------------------------
% 0.20/0.54  % (1059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (1059)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (1059)Memory used [KB]: 6268
% 0.20/0.54  % (1059)Time elapsed: 0.112 s
% 0.20/0.54  % (1059)------------------------------
% 0.20/0.54  % (1059)------------------------------
% 0.20/0.54  % (1071)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (1056)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (1053)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (1077)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (1060)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (1052)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (1039)Success in time 0.184 s
%------------------------------------------------------------------------------
