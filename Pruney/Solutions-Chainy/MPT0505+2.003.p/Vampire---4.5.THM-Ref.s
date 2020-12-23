%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   48 (  84 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 436 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
    inference(backward_demodulation,[],[f53,f191])).

fof(f191,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f171,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f13])).

fof(f13,plain,(
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

fof(f171,plain,(
    sP0(sK2,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( sP0(sK2,sK1,sK1)
    | sP0(sK2,sK1,sK1) ),
    inference(resolution,[],[f154,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK1,sK1),sK2)
      | sP0(X0,sK1,sK1) ) ),
    inference(resolution,[],[f66,f24])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f66,plain,(
    ! [X14,X12,X13] :
      ( ~ r1_tarski(X13,X14)
      | r2_hidden(sK4(X12,X13,X13),X14)
      | sP0(X12,X13,X13) ) ),
    inference(resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f154,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | sP0(X10,X11,X11) ) ),
    inference(subsumption_resolution,[],[f149,f33])).

fof(f149,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | ~ r2_hidden(sK4(X10,X11,X11),X11)
      | sP0(X10,X11,X11) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | ~ r2_hidden(sK4(X10,X11,X11),X11)
      | sP0(X10,X11,X11)
      | sP0(X10,X11,X11) ) ),
    inference(resolution,[],[f35,f62])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f39,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f25,f51])).

fof(f51,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK3,X0),X1) = k7_relat_1(sK3,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f25,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (21174)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (21170)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (21177)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (21190)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (21172)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (21169)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (21198)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (21173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (21173)Refutation not found, incomplete strategy% (21173)------------------------------
% 0.20/0.51  % (21173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21173)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21173)Memory used [KB]: 6140
% 0.20/0.51  % (21173)Time elapsed: 0.106 s
% 0.20/0.51  % (21173)------------------------------
% 0.20/0.51  % (21173)------------------------------
% 0.20/0.51  % (21176)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (21182)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (21185)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (21175)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (21188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (21184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (21178)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (21176)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (21191)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (21171)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.54  % (21186)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.54  % (21197)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (21183)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f193,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(trivial_inequality_removal,[],[f192])).
% 1.40/0.54  fof(f192,plain,(
% 1.40/0.54    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1)),
% 1.40/0.54    inference(backward_demodulation,[],[f53,f191])).
% 1.40/0.54  fof(f191,plain,(
% 1.40/0.54    sK1 = k3_xboole_0(sK1,sK2)),
% 1.40/0.54    inference(resolution,[],[f171,f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.40/0.54    inference(cnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.40/0.54    inference(nnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.40/0.54    inference(definition_folding,[],[f2,f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.40/0.54  fof(f171,plain,(
% 1.40/0.54    sP0(sK2,sK1,sK1)),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f162])).
% 1.40/0.54  fof(f162,plain,(
% 1.40/0.54    sP0(sK2,sK1,sK1) | sP0(sK2,sK1,sK1)),
% 1.40/0.54    inference(resolution,[],[f154,f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X0] : (r2_hidden(sK4(X0,sK1,sK1),sK2) | sP0(X0,sK1,sK1)) )),
% 1.40/0.54    inference(resolution,[],[f66,f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    r1_tarski(sK1,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f10,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.40/0.54    inference(flattening,[],[f9])).
% 1.40/0.54  fof(f9,plain,(
% 1.40/0.54    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.40/0.54    inference(ennf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 1.40/0.54    inference(negated_conjecture,[],[f6])).
% 1.40/0.54  fof(f6,conjecture,(
% 1.40/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 1.40/0.54  fof(f66,plain,(
% 1.40/0.54    ( ! [X14,X12,X13] : (~r1_tarski(X13,X14) | r2_hidden(sK4(X12,X13,X13),X14) | sP0(X12,X13,X13)) )),
% 1.40/0.54    inference(resolution,[],[f62,f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,plain,(
% 1.40/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,plain,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.40/0.54    inference(factoring,[],[f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.40/0.54    inference(rectify,[],[f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.40/0.54    inference(flattening,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.40/0.54    inference(nnf_transformation,[],[f13])).
% 1.40/0.54  fof(f154,plain,(
% 1.40/0.54    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | sP0(X10,X11,X11)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f149,f33])).
% 1.40/0.54  fof(f149,plain,(
% 1.40/0.54    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | ~r2_hidden(sK4(X10,X11,X11),X11) | sP0(X10,X11,X11)) )),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f140])).
% 1.40/0.54  fof(f140,plain,(
% 1.40/0.54    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | ~r2_hidden(sK4(X10,X11,X11),X11) | sP0(X10,X11,X11) | sP0(X10,X11,X11)) )),
% 1.40/0.54    inference(resolution,[],[f35,f62])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k3_xboole_0(sK1,sK2))),
% 1.40/0.54    inference(forward_demodulation,[],[f52,f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.40/0.54    inference(superposition,[],[f39,f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.40/0.54    inference(superposition,[],[f27,f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k3_xboole_0(sK2,sK1))),
% 1.40/0.54    inference(superposition,[],[f25,f51])).
% 1.40/0.54  fof(f51,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK3,X0),X1) = k7_relat_1(sK3,k3_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(resolution,[],[f29,f23])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    v1_relat_1(sK3)),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.40/0.54    inference(ennf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (21176)------------------------------
% 1.40/0.54  % (21176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21176)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (21176)Memory used [KB]: 6396
% 1.40/0.54  % (21176)Time elapsed: 0.131 s
% 1.40/0.54  % (21176)------------------------------
% 1.40/0.54  % (21176)------------------------------
% 1.40/0.54  % (21189)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (21189)Refutation not found, incomplete strategy% (21189)------------------------------
% 1.40/0.54  % (21189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21181)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (21180)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (21191)Refutation not found, incomplete strategy% (21191)------------------------------
% 1.40/0.54  % (21191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21191)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (21191)Memory used [KB]: 10618
% 1.40/0.54  % (21191)Time elapsed: 0.099 s
% 1.40/0.54  % (21191)------------------------------
% 1.40/0.54  % (21191)------------------------------
% 1.40/0.54  % (21195)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (21196)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (21193)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  % (21194)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (21168)Success in time 0.188 s
%------------------------------------------------------------------------------
