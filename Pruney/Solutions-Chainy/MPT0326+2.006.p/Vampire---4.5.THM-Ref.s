%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:46 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 107 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 360 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(subsumption_resolution,[],[f202,f57])).

% (9666)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f55,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (9668)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f202,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f201])).

fof(f201,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f54,f182])).

fof(f182,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f180,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f41,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f159,f149])).

fof(f149,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    inference(resolution,[],[f147,f34])).

fof(f34,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).

% (9652)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f20,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))
      | k1_xboole_0 = k2_zfmisc_1(sK1,X0) ) ),
    inference(resolution,[],[f36,f35])).

fof(f35,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
      | k1_xboole_0 = k2_zfmisc_1(X0,sK1) ) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    r2_hidden(sK4(sK1,sK3),sK1) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:33:39 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.48  % (9656)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.49  % (9655)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.49  % (9662)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.49  % (9664)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.49  % (9669)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.49  % (9671)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.50  % (9680)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.50  % (9654)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.50  % (9674)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.50  % (9656)Refutation found. Thanks to Tanya!
% 0.18/0.50  % SZS status Theorem for theBenchmark
% 0.18/0.50  % SZS output start Proof for theBenchmark
% 0.18/0.50  fof(f209,plain,(
% 0.18/0.50    $false),
% 0.18/0.50    inference(subsumption_resolution,[],[f202,f57])).
% 0.18/0.50  % (9666)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.50  fof(f57,plain,(
% 0.18/0.50    v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(resolution,[],[f56,f44])).
% 0.18/0.50  fof(f44,plain,(
% 0.18/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f30])).
% 0.18/0.50  fof(f30,plain,(
% 0.18/0.50    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK5(X0),X0))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f29])).
% 0.18/0.50  fof(f29,plain,(
% 0.18/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f17,plain,(
% 0.18/0.50    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.18/0.50    inference(ennf_transformation,[],[f12])).
% 0.18/0.50  fof(f12,plain,(
% 0.18/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.18/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.50  fof(f1,axiom,(
% 0.18/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.50  fof(f56,plain,(
% 0.18/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.50    inference(forward_demodulation,[],[f55,f45])).
% 0.18/0.50  fof(f45,plain,(
% 0.18/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.18/0.50    inference(cnf_transformation,[],[f10])).
% 0.18/0.50  fof(f10,plain,(
% 0.18/0.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.18/0.50    inference(rectify,[],[f3])).
% 0.18/0.50  fof(f3,axiom,(
% 0.18/0.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.18/0.50  fof(f55,plain,(
% 0.18/0.50    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.18/0.50    inference(resolution,[],[f49,f52])).
% 0.18/0.50  fof(f52,plain,(
% 0.18/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.18/0.50    inference(equality_resolution,[],[f46])).
% 0.18/0.50  fof(f46,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f18])).
% 0.18/0.50  % (9668)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.50  fof(f18,plain,(
% 0.18/0.50    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.18/0.50    inference(ennf_transformation,[],[f5])).
% 0.18/0.50  fof(f5,axiom,(
% 0.18/0.50    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.18/0.50  fof(f49,plain,(
% 0.18/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f32])).
% 0.18/0.50  fof(f32,plain,(
% 0.18/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f31])).
% 0.18/0.50  fof(f31,plain,(
% 0.18/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f19,plain,(
% 0.18/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(ennf_transformation,[],[f11])).
% 0.18/0.50  fof(f11,plain,(
% 0.18/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(rectify,[],[f4])).
% 0.18/0.50  fof(f4,axiom,(
% 0.18/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.18/0.50  fof(f202,plain,(
% 0.18/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(backward_demodulation,[],[f33,f201])).
% 0.18/0.50  fof(f201,plain,(
% 0.18/0.50    k1_xboole_0 = sK0),
% 0.18/0.50    inference(subsumption_resolution,[],[f185,f56])).
% 0.18/0.50  fof(f185,plain,(
% 0.18/0.50    r2_hidden(sK4(k1_xboole_0,sK3),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.18/0.50    inference(superposition,[],[f54,f182])).
% 0.18/0.50  fof(f182,plain,(
% 0.18/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.18/0.50    inference(subsumption_resolution,[],[f180,f41])).
% 0.18/0.50  fof(f41,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.18/0.50    inference(cnf_transformation,[],[f28])).
% 0.18/0.50  fof(f28,plain,(
% 0.18/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.50    inference(flattening,[],[f27])).
% 0.18/0.50  fof(f27,plain,(
% 0.18/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.50    inference(nnf_transformation,[],[f6])).
% 0.18/0.50  fof(f6,axiom,(
% 0.18/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.50  fof(f180,plain,(
% 0.18/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.50    inference(trivial_inequality_removal,[],[f179])).
% 0.18/0.50  fof(f179,plain,(
% 0.18/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.50    inference(superposition,[],[f41,f164])).
% 0.18/0.50  fof(f164,plain,(
% 0.18/0.50    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.50    inference(resolution,[],[f159,f149])).
% 0.18/0.50  fof(f149,plain,(
% 0.18/0.50    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.18/0.50    inference(resolution,[],[f147,f34])).
% 0.18/0.50  fof(f34,plain,(
% 0.18/0.50    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f22,plain,(
% 0.18/0.50    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).
% 0.18/0.50  % (9652)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.50  fof(f20,plain,(
% 0.18/0.50    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f21,plain,(
% 0.18/0.50    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f13,plain,(
% 0.18/0.50    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.18/0.50    inference(ennf_transformation,[],[f9])).
% 0.18/0.50  fof(f9,negated_conjecture,(
% 0.18/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.18/0.50    inference(negated_conjecture,[],[f8])).
% 0.18/0.50  fof(f8,conjecture,(
% 0.18/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.18/0.50  fof(f147,plain,(
% 0.18/0.50    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) | k1_xboole_0 = k2_zfmisc_1(sK1,X0)) )),
% 0.18/0.50    inference(resolution,[],[f36,f35])).
% 0.18/0.50  fof(f35,plain,(
% 0.18/0.50    ~r1_tarski(sK1,sK3)),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  fof(f36,plain,(
% 0.18/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f15])).
% 0.18/0.50  fof(f15,plain,(
% 0.18/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.18/0.50    inference(flattening,[],[f14])).
% 0.18/0.50  fof(f14,plain,(
% 0.18/0.50    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.18/0.50    inference(ennf_transformation,[],[f7])).
% 0.18/0.50  fof(f7,axiom,(
% 0.18/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.18/0.50  fof(f159,plain,(
% 0.18/0.50    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | k1_xboole_0 = k2_zfmisc_1(X0,sK1)) )),
% 0.18/0.50    inference(resolution,[],[f37,f35])).
% 0.18/0.50  fof(f37,plain,(
% 0.18/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f15])).
% 0.18/0.50  fof(f54,plain,(
% 0.18/0.50    r2_hidden(sK4(sK1,sK3),sK1)),
% 0.18/0.50    inference(resolution,[],[f39,f35])).
% 0.18/0.50  fof(f39,plain,(
% 0.18/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f26])).
% 0.18/0.50  fof(f26,plain,(
% 0.18/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.18/0.50  fof(f25,plain,(
% 0.18/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f24,plain,(
% 0.18/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.50    inference(rectify,[],[f23])).
% 0.18/0.50  fof(f23,plain,(
% 0.18/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.50    inference(nnf_transformation,[],[f16])).
% 0.18/0.50  fof(f16,plain,(
% 0.18/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.50    inference(ennf_transformation,[],[f2])).
% 0.18/0.50  fof(f2,axiom,(
% 0.18/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.50  fof(f33,plain,(
% 0.18/0.50    ~v1_xboole_0(sK0)),
% 0.18/0.50    inference(cnf_transformation,[],[f22])).
% 0.18/0.50  % SZS output end Proof for theBenchmark
% 0.18/0.50  % (9656)------------------------------
% 0.18/0.50  % (9656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (9656)Termination reason: Refutation
% 0.18/0.50  
% 0.18/0.50  % (9656)Memory used [KB]: 6396
% 0.18/0.50  % (9656)Time elapsed: 0.103 s
% 0.18/0.50  % (9656)------------------------------
% 0.18/0.50  % (9656)------------------------------
% 0.18/0.50  % (9668)Refutation not found, incomplete strategy% (9668)------------------------------
% 0.18/0.50  % (9668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (9668)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (9668)Memory used [KB]: 10618
% 0.18/0.50  % (9668)Time elapsed: 0.116 s
% 0.18/0.50  % (9668)------------------------------
% 0.18/0.50  % (9668)------------------------------
% 0.18/0.50  % (9658)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.51  % (9653)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (9650)Success in time 0.172 s
%------------------------------------------------------------------------------
