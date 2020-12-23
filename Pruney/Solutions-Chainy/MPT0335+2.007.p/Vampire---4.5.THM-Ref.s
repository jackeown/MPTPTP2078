%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 102 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 308 expanded)
%              Number of equality atoms :  101 ( 176 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f820,plain,(
    $false ),
    inference(subsumption_resolution,[],[f819,f50])).

fof(f50,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k1_tarski(sK5) = k3_xboole_0(sK3,sK4)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k1_tarski(sK5) = k3_xboole_0(sK3,sK4)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f819,plain,(
    k3_xboole_0(sK2,sK4) = k1_tarski(sK5) ),
    inference(forward_demodulation,[],[f818,f228])).

fof(f228,plain,(
    k1_tarski(sK5) = k3_xboole_0(sK2,k1_tarski(sK5)) ),
    inference(backward_demodulation,[],[f213,f227])).

fof(f227,plain,(
    ! [X6] : k1_tarski(X6) = k4_xboole_0(k1_tarski(X6),k1_xboole_0) ),
    inference(forward_demodulation,[],[f220,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f220,plain,(
    ! [X6] : k3_xboole_0(k1_tarski(X6),k1_tarski(X6)) = k4_xboole_0(k1_tarski(X6),k1_xboole_0) ),
    inference(superposition,[],[f56,f198])).

fof(f198,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(resolution,[],[f86,f92])).

fof(f92,plain,(
    ! [X0] : sP0(X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f88,f51])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f88,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f11,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f86,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK7(X0,X1,X2) != X0
              & sK7(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X0
            | sK7(X0,X1,X2) = X1
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X0
            & sK7(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X0
          | sK7(X0,X1,X2) = X1
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f213,plain,(
    k3_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(k1_tarski(sK5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f208,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f208,plain,(
    k3_xboole_0(k1_tarski(sK5),sK2) = k4_xboole_0(k1_tarski(sK5),k1_xboole_0) ),
    inference(superposition,[],[f56,f197])).

fof(f197,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK2) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f818,plain,(
    k3_xboole_0(sK2,sK4) = k3_xboole_0(sK2,k1_tarski(sK5)) ),
    inference(forward_demodulation,[],[f811,f56])).

fof(f811,plain,(
    k3_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(superposition,[],[f56,f743])).

fof(f743,plain,(
    k4_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(sK2,sK4) ),
    inference(forward_demodulation,[],[f727,f655])).

fof(f655,plain,(
    ! [X19] : k3_xboole_0(sK2,k4_xboole_0(sK3,X19)) = k4_xboole_0(sK2,X19) ),
    inference(superposition,[],[f66,f99])).

fof(f99,plain,(
    sK2 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f727,plain,(
    k4_xboole_0(sK2,k1_tarski(sK5)) = k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(superposition,[],[f655,f105])).

fof(f105,plain,(
    k4_xboole_0(sK3,sK4) = k4_xboole_0(sK3,k1_tarski(sK5)) ),
    inference(superposition,[],[f55,f48])).

fof(f48,plain,(
    k1_tarski(sK5) = k3_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:27:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (11801)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (11793)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (11791)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (11817)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (11790)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (11788)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (11800)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11792)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (11789)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (11814)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (11816)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (11813)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (11818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (11815)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (11806)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (11809)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (11797)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (11808)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (11810)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (11799)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (11796)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (11798)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (11807)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (11805)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (11802)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (11812)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.58  % (11811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.58  % (11803)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.59  % (11794)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.73/0.59  % (11795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.14/0.65  % (11795)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.14/0.65  % SZS output start Proof for theBenchmark
% 2.14/0.65  fof(f820,plain,(
% 2.14/0.65    $false),
% 2.14/0.65    inference(subsumption_resolution,[],[f819,f50])).
% 2.14/0.65  fof(f50,plain,(
% 2.14/0.65    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f27,plain,(
% 2.14/0.65    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k1_tarski(sK5) = k3_xboole_0(sK3,sK4) & r1_tarski(sK2,sK3)),
% 2.14/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f26])).
% 2.14/0.65  fof(f26,plain,(
% 2.14/0.65    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k1_tarski(sK5) = k3_xboole_0(sK3,sK4) & r1_tarski(sK2,sK3))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f19,plain,(
% 2.14/0.65    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.14/0.65    inference(flattening,[],[f18])).
% 2.14/0.65  fof(f18,plain,(
% 2.14/0.65    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.14/0.65    inference(ennf_transformation,[],[f16])).
% 2.14/0.65  fof(f16,negated_conjecture,(
% 2.14/0.65    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 2.14/0.65    inference(negated_conjecture,[],[f15])).
% 2.14/0.65  fof(f15,conjecture,(
% 2.14/0.65    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.14/0.65  fof(f819,plain,(
% 2.14/0.65    k3_xboole_0(sK2,sK4) = k1_tarski(sK5)),
% 2.14/0.65    inference(forward_demodulation,[],[f818,f228])).
% 2.14/0.65  fof(f228,plain,(
% 2.14/0.65    k1_tarski(sK5) = k3_xboole_0(sK2,k1_tarski(sK5))),
% 2.14/0.65    inference(backward_demodulation,[],[f213,f227])).
% 2.14/0.65  fof(f227,plain,(
% 2.14/0.65    ( ! [X6] : (k1_tarski(X6) = k4_xboole_0(k1_tarski(X6),k1_xboole_0)) )),
% 2.14/0.65    inference(forward_demodulation,[],[f220,f52])).
% 2.14/0.65  fof(f52,plain,(
% 2.14/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.14/0.65    inference(cnf_transformation,[],[f17])).
% 2.14/0.65  fof(f17,plain,(
% 2.14/0.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.65    inference(rectify,[],[f4])).
% 2.14/0.65  fof(f4,axiom,(
% 2.14/0.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.14/0.65  fof(f220,plain,(
% 2.14/0.65    ( ! [X6] : (k3_xboole_0(k1_tarski(X6),k1_tarski(X6)) = k4_xboole_0(k1_tarski(X6),k1_xboole_0)) )),
% 2.14/0.65    inference(superposition,[],[f56,f198])).
% 2.14/0.65  fof(f198,plain,(
% 2.14/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.14/0.65    inference(resolution,[],[f65,f94])).
% 2.14/0.65  fof(f94,plain,(
% 2.14/0.65    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 2.14/0.65    inference(resolution,[],[f86,f92])).
% 2.14/0.65  fof(f92,plain,(
% 2.14/0.65    ( ! [X0] : (sP0(X0,X0,k1_tarski(X0))) )),
% 2.14/0.65    inference(superposition,[],[f88,f51])).
% 2.14/0.65  fof(f51,plain,(
% 2.14/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f12])).
% 2.14/0.65  fof(f12,axiom,(
% 2.14/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.14/0.65  fof(f88,plain,(
% 2.14/0.65    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 2.14/0.65    inference(equality_resolution,[],[f74])).
% 2.14/0.65  fof(f74,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 2.14/0.65    inference(cnf_transformation,[],[f40])).
% 2.14/0.65  fof(f40,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 2.14/0.65    inference(nnf_transformation,[],[f23])).
% 2.14/0.65  fof(f23,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.14/0.65    inference(definition_folding,[],[f11,f22])).
% 2.14/0.65  fof(f22,plain,(
% 2.14/0.65    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.14/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.14/0.65  fof(f11,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.14/0.65  fof(f86,plain,(
% 2.14/0.65    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 2.14/0.65    inference(equality_resolution,[],[f70])).
% 2.14/0.65  fof(f70,plain,(
% 2.14/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f39])).
% 2.14/0.65  fof(f39,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.14/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 2.14/0.65  fof(f38,plain,(
% 2.14/0.65    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f37,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.14/0.65    inference(rectify,[],[f36])).
% 2.14/0.65  fof(f36,plain,(
% 2.14/0.65    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.14/0.65    inference(flattening,[],[f35])).
% 2.14/0.65  fof(f35,plain,(
% 2.14/0.65    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.14/0.65    inference(nnf_transformation,[],[f22])).
% 2.14/0.65  fof(f65,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 2.14/0.65    inference(cnf_transformation,[],[f34])).
% 2.14/0.65  fof(f34,plain,(
% 2.14/0.65    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 2.14/0.65    inference(nnf_transformation,[],[f14])).
% 2.14/0.65  fof(f14,axiom,(
% 2.14/0.65    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 2.14/0.65  fof(f56,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f8])).
% 2.14/0.65  fof(f8,axiom,(
% 2.14/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.14/0.65  fof(f213,plain,(
% 2.14/0.65    k3_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(k1_tarski(sK5),k1_xboole_0)),
% 2.14/0.65    inference(forward_demodulation,[],[f208,f53])).
% 2.14/0.65  fof(f53,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f1])).
% 2.14/0.65  fof(f1,axiom,(
% 2.14/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.65  fof(f208,plain,(
% 2.14/0.65    k3_xboole_0(k1_tarski(sK5),sK2) = k4_xboole_0(k1_tarski(sK5),k1_xboole_0)),
% 2.14/0.65    inference(superposition,[],[f56,f197])).
% 2.14/0.65  fof(f197,plain,(
% 2.14/0.65    k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK2)),
% 2.14/0.65    inference(resolution,[],[f65,f49])).
% 2.14/0.65  fof(f49,plain,(
% 2.14/0.65    r2_hidden(sK5,sK2)),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f818,plain,(
% 2.14/0.65    k3_xboole_0(sK2,sK4) = k3_xboole_0(sK2,k1_tarski(sK5))),
% 2.14/0.65    inference(forward_demodulation,[],[f811,f56])).
% 2.14/0.65  fof(f811,plain,(
% 2.14/0.65    k3_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))),
% 2.14/0.65    inference(superposition,[],[f56,f743])).
% 2.14/0.65  fof(f743,plain,(
% 2.14/0.65    k4_xboole_0(sK2,k1_tarski(sK5)) = k4_xboole_0(sK2,sK4)),
% 2.14/0.65    inference(forward_demodulation,[],[f727,f655])).
% 2.14/0.65  fof(f655,plain,(
% 2.14/0.65    ( ! [X19] : (k3_xboole_0(sK2,k4_xboole_0(sK3,X19)) = k4_xboole_0(sK2,X19)) )),
% 2.14/0.65    inference(superposition,[],[f66,f99])).
% 2.14/0.65  fof(f99,plain,(
% 2.14/0.65    sK2 = k3_xboole_0(sK2,sK3)),
% 2.14/0.65    inference(resolution,[],[f57,f47])).
% 2.14/0.65  fof(f47,plain,(
% 2.14/0.65    r1_tarski(sK2,sK3)),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f57,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.14/0.65    inference(cnf_transformation,[],[f20])).
% 2.14/0.65  fof(f20,plain,(
% 2.14/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.14/0.65    inference(ennf_transformation,[],[f6])).
% 2.14/0.65  fof(f6,axiom,(
% 2.14/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.14/0.65  fof(f66,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f9,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.14/0.65  fof(f727,plain,(
% 2.14/0.65    k4_xboole_0(sK2,k1_tarski(sK5)) = k3_xboole_0(sK2,k4_xboole_0(sK3,sK4))),
% 2.14/0.65    inference(superposition,[],[f655,f105])).
% 2.14/0.65  fof(f105,plain,(
% 2.14/0.65    k4_xboole_0(sK3,sK4) = k4_xboole_0(sK3,k1_tarski(sK5))),
% 2.14/0.65    inference(superposition,[],[f55,f48])).
% 2.14/0.65  fof(f48,plain,(
% 2.14/0.65    k1_tarski(sK5) = k3_xboole_0(sK3,sK4)),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f55,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f7])).
% 2.14/0.65  fof(f7,axiom,(
% 2.14/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.14/0.65  % SZS output end Proof for theBenchmark
% 2.14/0.65  % (11795)------------------------------
% 2.14/0.65  % (11795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (11795)Termination reason: Refutation
% 2.14/0.65  
% 2.14/0.65  % (11795)Memory used [KB]: 6780
% 2.14/0.65  % (11795)Time elapsed: 0.236 s
% 2.14/0.65  % (11795)------------------------------
% 2.14/0.65  % (11795)------------------------------
% 2.14/0.65  % (11786)Success in time 0.286 s
%------------------------------------------------------------------------------
