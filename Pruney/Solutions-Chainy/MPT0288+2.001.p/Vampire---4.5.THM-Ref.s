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
% DateTime   : Thu Dec  3 12:41:43 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   71 (  99 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   18
%              Number of atoms          :  204 ( 280 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f542,f38])).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f542,plain,(
    r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
    | r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(resolution,[],[f452,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k3_tarski(X1)),X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f452,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK2)
      | r1_tarski(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f447,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f447,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK1)
      | r2_hidden(X12,sK2) ) ),
    inference(forward_demodulation,[],[f440,f39])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f440,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k4_xboole_0(sK1,k1_xboole_0))
      | r2_hidden(X12,sK2) ) ),
    inference(superposition,[],[f118,f410])).

fof(f410,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f362,f37])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f362,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f329,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f329,plain,(
    ! [X4,X3] :
      ( r1_tarski(k4_xboole_0(X4,X3),k1_xboole_0)
      | ~ r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f66,f310])).

fof(f310,plain,(
    ! [X2] : k3_tarski(k2_tarski(X2,k1_xboole_0)) = X2 ),
    inference(subsumption_resolution,[],[f305,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f305,plain,(
    ! [X2] :
      ( k3_tarski(k2_tarski(X2,k1_xboole_0)) = X2
      | ~ r1_tarski(X2,k3_tarski(k2_tarski(X2,k1_xboole_0))) ) ),
    inference(resolution,[],[f283,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f283,plain,(
    ! [X0] : r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0) ),
    inference(superposition,[],[f278,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f278,plain,(
    ! [X0] : r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),X0) ),
    inference(superposition,[],[f179,f39])).

fof(f179,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X7,X8)),X7),X8) ),
    inference(resolution,[],[f66,f70])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (31501)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (31510)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (31527)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (31527)Refutation not found, incomplete strategy% (31527)------------------------------
% 0.20/0.52  % (31527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31527)Memory used [KB]: 1663
% 0.20/0.52  % (31527)Time elapsed: 0.002 s
% 0.20/0.52  % (31527)------------------------------
% 0.20/0.52  % (31527)------------------------------
% 0.20/0.53  % (31521)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (31512)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (31498)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (31498)Refutation not found, incomplete strategy% (31498)------------------------------
% 0.20/0.54  % (31498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31498)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31498)Memory used [KB]: 1663
% 0.20/0.54  % (31498)Time elapsed: 0.125 s
% 0.20/0.54  % (31498)------------------------------
% 0.20/0.54  % (31498)------------------------------
% 0.20/0.54  % (31502)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (31522)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (31499)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (31500)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (31523)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (31497)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (31511)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (31511)Refutation not found, incomplete strategy% (31511)------------------------------
% 0.20/0.54  % (31511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31511)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31511)Memory used [KB]: 1663
% 0.20/0.54  % (31511)Time elapsed: 0.101 s
% 0.20/0.54  % (31511)------------------------------
% 0.20/0.54  % (31511)------------------------------
% 0.20/0.55  % (31506)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (31504)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (31515)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (31513)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (31518)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (31514)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (31513)Refutation not found, incomplete strategy% (31513)------------------------------
% 0.20/0.55  % (31513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31513)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31513)Memory used [KB]: 10618
% 0.20/0.55  % (31513)Time elapsed: 0.137 s
% 0.20/0.55  % (31513)------------------------------
% 0.20/0.55  % (31513)------------------------------
% 0.20/0.55  % (31514)Refutation not found, incomplete strategy% (31514)------------------------------
% 0.20/0.55  % (31514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31514)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31514)Memory used [KB]: 1663
% 0.20/0.55  % (31514)Time elapsed: 0.137 s
% 0.20/0.55  % (31514)------------------------------
% 0.20/0.55  % (31514)------------------------------
% 0.20/0.55  % (31517)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (31509)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (31505)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (31508)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (31509)Refutation not found, incomplete strategy% (31509)------------------------------
% 0.20/0.56  % (31509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31509)Memory used [KB]: 10618
% 0.20/0.56  % (31509)Time elapsed: 0.149 s
% 0.20/0.56  % (31509)------------------------------
% 0.20/0.56  % (31509)------------------------------
% 0.20/0.56  % (31507)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (31525)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.56  % (31507)Refutation not found, incomplete strategy% (31507)------------------------------
% 0.20/0.56  % (31507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31507)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31507)Memory used [KB]: 10746
% 0.20/0.56  % (31507)Time elapsed: 0.148 s
% 0.20/0.56  % (31507)------------------------------
% 0.20/0.56  % (31507)------------------------------
% 0.20/0.56  % (31526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (31524)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (31526)Refutation not found, incomplete strategy% (31526)------------------------------
% 0.20/0.56  % (31526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31526)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31526)Memory used [KB]: 10746
% 0.20/0.56  % (31526)Time elapsed: 0.149 s
% 0.20/0.56  % (31526)------------------------------
% 0.20/0.56  % (31526)------------------------------
% 0.20/0.56  % (31524)Refutation not found, incomplete strategy% (31524)------------------------------
% 0.20/0.56  % (31524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31524)Memory used [KB]: 6140
% 0.20/0.56  % (31524)Time elapsed: 0.148 s
% 0.20/0.56  % (31524)------------------------------
% 0.20/0.56  % (31524)------------------------------
% 0.20/0.57  % (31503)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (31519)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.59  % (31520)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.78/0.61  % (31503)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  fof(f543,plain,(
% 1.78/0.61    $false),
% 1.78/0.61    inference(subsumption_resolution,[],[f542,f38])).
% 1.78/0.61  fof(f38,plain,(
% 1.78/0.61    ~r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 1.78/0.61    inference(cnf_transformation,[],[f26])).
% 1.78/0.61  fof(f26,plain,(
% 1.78/0.61    ~r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) & r1_tarski(sK1,sK2)),
% 1.78/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f25])).
% 1.78/0.61  fof(f25,plain,(
% 1.78/0.61    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1)) => (~r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) & r1_tarski(sK1,sK2))),
% 1.78/0.61    introduced(choice_axiom,[])).
% 1.78/0.61  fof(f17,plain,(
% 1.78/0.61    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1))),
% 1.78/0.61    inference(ennf_transformation,[],[f16])).
% 1.78/0.61  fof(f16,negated_conjecture,(
% 1.78/0.61    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.78/0.61    inference(negated_conjecture,[],[f15])).
% 1.78/0.61  fof(f15,conjecture,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.78/0.61  fof(f542,plain,(
% 1.78/0.61    r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 1.78/0.61    inference(duplicate_literal_removal,[],[f541])).
% 1.78/0.61  fof(f541,plain,(
% 1.78/0.61    r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) | r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 1.78/0.61    inference(resolution,[],[f452,f88])).
% 1.78/0.61  fof(f88,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k3_tarski(X1)),X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 1.78/0.61    inference(resolution,[],[f49,f47])).
% 1.78/0.61  fof(f47,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f19])).
% 1.78/0.61  fof(f19,plain,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.78/0.61    inference(ennf_transformation,[],[f12])).
% 1.78/0.61  fof(f12,axiom,(
% 1.78/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.78/0.61  fof(f49,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(sK3(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f28])).
% 1.78/0.61  fof(f28,plain,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.78/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).
% 1.78/0.61  fof(f27,plain,(
% 1.78/0.61    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.78/0.61    introduced(choice_axiom,[])).
% 1.78/0.61  fof(f20,plain,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.78/0.61    inference(ennf_transformation,[],[f14])).
% 1.78/0.61  fof(f14,axiom,(
% 1.78/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.78/0.61  fof(f452,plain,(
% 1.78/0.61    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK2) | r1_tarski(k3_tarski(sK1),X0)) )),
% 1.78/0.61    inference(resolution,[],[f447,f48])).
% 1.78/0.61  fof(f48,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f28])).
% 1.78/0.61  fof(f447,plain,(
% 1.78/0.61    ( ! [X12] : (~r2_hidden(X12,sK1) | r2_hidden(X12,sK2)) )),
% 1.78/0.61    inference(forward_demodulation,[],[f440,f39])).
% 1.78/0.61  fof(f39,plain,(
% 1.78/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.78/0.61    inference(cnf_transformation,[],[f7])).
% 1.78/0.61  fof(f7,axiom,(
% 1.78/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.78/0.61  fof(f440,plain,(
% 1.78/0.61    ( ! [X12] : (~r2_hidden(X12,k4_xboole_0(sK1,k1_xboole_0)) | r2_hidden(X12,sK2)) )),
% 1.78/0.61    inference(superposition,[],[f118,f410])).
% 1.78/0.61  fof(f410,plain,(
% 1.78/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.78/0.61    inference(resolution,[],[f362,f37])).
% 1.78/0.61  fof(f37,plain,(
% 1.78/0.61    r1_tarski(sK1,sK2)),
% 1.78/0.61    inference(cnf_transformation,[],[f26])).
% 1.78/0.61  fof(f362,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.78/0.61    inference(resolution,[],[f329,f40])).
% 1.78/0.61  fof(f40,plain,(
% 1.78/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.78/0.61    inference(cnf_transformation,[],[f18])).
% 1.78/0.61  fof(f18,plain,(
% 1.78/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.78/0.61    inference(ennf_transformation,[],[f8])).
% 1.78/0.61  fof(f8,axiom,(
% 1.78/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.78/0.61  fof(f329,plain,(
% 1.78/0.61    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X4,X3),k1_xboole_0) | ~r1_tarski(X4,X3)) )),
% 1.78/0.61    inference(superposition,[],[f66,f310])).
% 1.78/0.61  fof(f310,plain,(
% 1.78/0.61    ( ! [X2] : (k3_tarski(k2_tarski(X2,k1_xboole_0)) = X2) )),
% 1.78/0.61    inference(subsumption_resolution,[],[f305,f103])).
% 1.78/0.61  fof(f103,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.78/0.61    inference(resolution,[],[f67,f70])).
% 1.78/0.61  fof(f70,plain,(
% 1.78/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.78/0.61    inference(equality_resolution,[],[f51])).
% 1.78/0.61  fof(f51,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.78/0.61    inference(cnf_transformation,[],[f30])).
% 1.78/0.61  fof(f30,plain,(
% 1.78/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.61    inference(flattening,[],[f29])).
% 1.78/0.61  fof(f29,plain,(
% 1.78/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.61    inference(nnf_transformation,[],[f3])).
% 1.78/0.61  fof(f3,axiom,(
% 1.78/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.61  fof(f67,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f54,f44])).
% 1.78/0.61  fof(f44,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f13])).
% 1.78/0.61  fof(f13,axiom,(
% 1.78/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.78/0.61  fof(f54,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f22])).
% 1.78/0.61  fof(f22,plain,(
% 1.78/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.78/0.61    inference(ennf_transformation,[],[f5])).
% 1.78/0.61  fof(f5,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.78/0.61  fof(f305,plain,(
% 1.78/0.61    ( ! [X2] : (k3_tarski(k2_tarski(X2,k1_xboole_0)) = X2 | ~r1_tarski(X2,k3_tarski(k2_tarski(X2,k1_xboole_0)))) )),
% 1.78/0.61    inference(resolution,[],[f283,f52])).
% 1.78/0.61  fof(f52,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f30])).
% 1.78/0.61  fof(f283,plain,(
% 1.78/0.61    ( ! [X0] : (r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0)) )),
% 1.78/0.61    inference(superposition,[],[f278,f42])).
% 1.78/0.61  fof(f42,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f11])).
% 1.78/0.61  fof(f11,axiom,(
% 1.78/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.78/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.78/0.61  fof(f278,plain,(
% 1.78/0.61    ( ! [X0] : (r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),X0)) )),
% 1.78/0.61    inference(superposition,[],[f179,f39])).
% 1.78/0.61  fof(f179,plain,(
% 1.78/0.61    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X7,X8)),X7),X8)) )),
% 1.78/0.61    inference(resolution,[],[f66,f70])).
% 1.90/0.62  fof(f66,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f53,f44])).
% 1.90/0.62  fof(f53,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f21])).
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f9])).
% 1.90/0.62  fof(f9,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.90/0.62  fof(f118,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r2_hidden(X0,X2)) )),
% 1.90/0.62    inference(resolution,[],[f56,f72])).
% 1.90/0.62  fof(f72,plain,(
% 1.90/0.62    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.90/0.62    inference(equality_resolution,[],[f69])).
% 1.90/0.62  fof(f69,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.90/0.62    inference(definition_unfolding,[],[f61,f46])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.90/0.62  fof(f61,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.90/0.62    inference(cnf_transformation,[],[f36])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.90/0.62    inference(nnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.90/0.62    inference(definition_folding,[],[f2,f23])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.90/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.90/0.62  fof(f56,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f35])).
% 1.90/0.62  fof(f35,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.90/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.90/0.62    introduced(choice_axiom,[])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.90/0.62    inference(rectify,[],[f32])).
% 1.90/0.62  fof(f32,plain,(
% 1.90/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.90/0.62    inference(flattening,[],[f31])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.90/0.62    inference(nnf_transformation,[],[f23])).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (31503)------------------------------
% 1.90/0.62  % (31503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (31503)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (31503)Memory used [KB]: 11001
% 1.90/0.62  % (31503)Time elapsed: 0.178 s
% 1.90/0.62  % (31503)------------------------------
% 1.90/0.62  % (31503)------------------------------
% 1.90/0.62  % (31496)Success in time 0.255 s
%------------------------------------------------------------------------------
