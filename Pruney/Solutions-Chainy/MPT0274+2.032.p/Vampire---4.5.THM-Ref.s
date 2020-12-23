%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:25 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 184 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  161 ( 608 expanded)
%              Number of equality atoms :   57 ( 192 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1807,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1802,f129])).

fof(f129,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f126,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f126,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f122,f62])).

fof(f62,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f122,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f69,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f1802,plain,(
    r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f468,f1801])).

fof(f1801,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1799])).

fof(f1799,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f565,f608])).

fof(f608,plain,(
    k2_tarski(sK0,sK1) = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f607,f129])).

fof(f607,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK0)
    | r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f606,f468])).

fof(f606,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK0)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f567])).

fof(f567,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK0)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f107,f63])).

fof(f63,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f565,plain,(
    ! [X19,X18] :
      ( k1_tarski(X18) != k2_tarski(X18,X19)
      | X18 = X19 ) ),
    inference(subsumption_resolution,[],[f562,f130])).

fof(f130,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f120,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f120,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f562,plain,(
    ! [X19,X18] :
      ( k1_tarski(X18) != k2_tarski(X18,X19)
      | r2_hidden(X19,k1_xboole_0)
      | X18 = X19 ) ),
    inference(superposition,[],[f106,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f468,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f467,f129])).

fof(f467,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f464])).

fof(f464,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f109,f144])).

fof(f144,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f143,f129])).

fof(f143,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f64,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f64,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:59:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.49  % (9459)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (9463)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.50  % (9460)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  % (9454)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.51  % (9475)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.51  % (9461)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.51  % (9462)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (9476)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (9479)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (9456)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (9455)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (9467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (9472)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.52  % (9469)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.52  % (9477)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.52  % (9471)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (9453)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (9469)Refutation not found, incomplete strategy% (9469)------------------------------
% 0.19/0.53  % (9469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9469)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9469)Memory used [KB]: 10746
% 0.19/0.53  % (9469)Time elapsed: 0.130 s
% 0.19/0.53  % (9469)------------------------------
% 0.19/0.53  % (9469)------------------------------
% 0.19/0.53  % (9468)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.53  % (9478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (9457)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (9464)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.54  % (9470)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  % (9473)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (9481)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.55  % (9465)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.55  % (9482)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.55  % (9482)Refutation not found, incomplete strategy% (9482)------------------------------
% 0.19/0.55  % (9482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (9474)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.55  % (9466)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.56  % (9480)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.57  % (9458)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.57  % (9482)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (9482)Memory used [KB]: 1663
% 0.19/0.57  % (9482)Time elapsed: 0.120 s
% 0.19/0.57  % (9482)------------------------------
% 0.19/0.57  % (9482)------------------------------
% 1.93/0.59  % (9462)Refutation found. Thanks to Tanya!
% 1.93/0.59  % SZS status Theorem for theBenchmark
% 1.93/0.60  % SZS output start Proof for theBenchmark
% 1.93/0.60  fof(f1807,plain,(
% 1.93/0.60    $false),
% 1.93/0.60    inference(subsumption_resolution,[],[f1802,f129])).
% 1.93/0.60  fof(f129,plain,(
% 1.93/0.60    ~r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(subsumption_resolution,[],[f126,f110])).
% 1.93/0.60  fof(f110,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f37])).
% 1.93/0.60  fof(f37,plain,(
% 1.93/0.60    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.93/0.60    inference(ennf_transformation,[],[f20])).
% 1.93/0.60  fof(f20,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.93/0.60  fof(f126,plain,(
% 1.93/0.60    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(superposition,[],[f122,f62])).
% 1.93/0.60  fof(f62,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(cnf_transformation,[],[f41])).
% 1.93/0.60  fof(f41,plain,(
% 1.93/0.60    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.93/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f40])).
% 1.93/0.60  fof(f40,plain,(
% 1.93/0.60    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.93/0.60    introduced(choice_axiom,[])).
% 1.93/0.60  fof(f39,plain,(
% 1.93/0.60    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.93/0.60    inference(flattening,[],[f38])).
% 1.93/0.60  fof(f38,plain,(
% 1.93/0.60    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.93/0.60    inference(nnf_transformation,[],[f30])).
% 1.93/0.60  fof(f30,plain,(
% 1.93/0.60    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.93/0.60    inference(ennf_transformation,[],[f27])).
% 1.93/0.60  fof(f27,negated_conjecture,(
% 1.93/0.60    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.93/0.60    inference(negated_conjecture,[],[f26])).
% 1.93/0.60  fof(f26,conjecture,(
% 1.93/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.93/0.60  fof(f122,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.93/0.60    inference(backward_demodulation,[],[f69,f74])).
% 1.93/0.60  fof(f74,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.93/0.60    inference(cnf_transformation,[],[f11])).
% 1.93/0.60  fof(f11,axiom,(
% 1.93/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.93/0.60  fof(f69,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f15])).
% 1.93/0.60  fof(f15,axiom,(
% 1.93/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.93/0.60  fof(f1802,plain,(
% 1.93/0.60    r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(backward_demodulation,[],[f468,f1801])).
% 1.93/0.60  fof(f1801,plain,(
% 1.93/0.60    sK0 = sK1),
% 1.93/0.60    inference(trivial_inequality_removal,[],[f1799])).
% 1.93/0.60  fof(f1799,plain,(
% 1.93/0.60    k1_tarski(sK0) != k1_tarski(sK0) | sK0 = sK1),
% 1.93/0.60    inference(superposition,[],[f565,f608])).
% 1.93/0.60  fof(f608,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK0)),
% 1.93/0.60    inference(subsumption_resolution,[],[f607,f129])).
% 1.93/0.60  fof(f607,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK0) | r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(subsumption_resolution,[],[f606,f468])).
% 1.93/0.60  fof(f606,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK0) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(duplicate_literal_removal,[],[f567])).
% 1.93/0.60  fof(f567,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK0) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(superposition,[],[f107,f63])).
% 1.93/0.60  fof(f63,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(cnf_transformation,[],[f41])).
% 1.93/0.60  fof(f107,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f61])).
% 1.93/0.60  fof(f61,plain,(
% 1.93/0.60    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.93/0.60    inference(flattening,[],[f60])).
% 1.93/0.60  fof(f60,plain,(
% 1.93/0.60    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.93/0.60    inference(nnf_transformation,[],[f25])).
% 1.93/0.60  fof(f25,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 1.93/0.60  fof(f565,plain,(
% 1.93/0.60    ( ! [X19,X18] : (k1_tarski(X18) != k2_tarski(X18,X19) | X18 = X19) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f562,f130])).
% 1.93/0.60  fof(f130,plain,(
% 1.93/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.93/0.60    inference(superposition,[],[f120,f65])).
% 1.93/0.60  fof(f65,plain,(
% 1.93/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f13])).
% 1.93/0.60  fof(f13,axiom,(
% 1.93/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.93/0.60  fof(f120,plain,(
% 1.93/0.60    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.93/0.60    inference(equality_resolution,[],[f103])).
% 1.93/0.60  fof(f103,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.93/0.60    inference(cnf_transformation,[],[f59])).
% 1.93/0.60  fof(f59,plain,(
% 1.93/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.93/0.60    inference(flattening,[],[f58])).
% 1.93/0.60  fof(f58,plain,(
% 1.93/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.93/0.60    inference(nnf_transformation,[],[f23])).
% 1.93/0.60  fof(f23,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.93/0.60  fof(f562,plain,(
% 1.93/0.60    ( ! [X19,X18] : (k1_tarski(X18) != k2_tarski(X18,X19) | r2_hidden(X19,k1_xboole_0) | X18 = X19) )),
% 1.93/0.60    inference(superposition,[],[f106,f66])).
% 1.93/0.60  fof(f66,plain,(
% 1.93/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f7])).
% 1.93/0.60  fof(f7,axiom,(
% 1.93/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.93/0.60  fof(f106,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | X0 = X1) )),
% 1.93/0.60    inference(cnf_transformation,[],[f61])).
% 1.93/0.60  fof(f468,plain,(
% 1.93/0.60    r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(subsumption_resolution,[],[f467,f129])).
% 1.93/0.60  fof(f467,plain,(
% 1.93/0.60    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.93/0.60    inference(duplicate_literal_removal,[],[f464])).
% 1.93/0.60  fof(f464,plain,(
% 1.93/0.60    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(resolution,[],[f109,f144])).
% 1.93/0.60  fof(f144,plain,(
% 1.93/0.60    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(subsumption_resolution,[],[f143,f129])).
% 1.93/0.60  fof(f143,plain,(
% 1.93/0.60    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.93/0.60    inference(trivial_inequality_removal,[],[f139])).
% 1.93/0.60  fof(f139,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.93/0.60    inference(superposition,[],[f64,f82])).
% 1.93/0.60  fof(f82,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f46])).
% 1.93/0.60  fof(f46,plain,(
% 1.93/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.93/0.60    inference(nnf_transformation,[],[f14])).
% 1.93/0.60  fof(f14,axiom,(
% 1.93/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.93/0.60  fof(f64,plain,(
% 1.93/0.60    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.93/0.60    inference(cnf_transformation,[],[f41])).
% 1.93/0.60  fof(f109,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f36])).
% 1.93/0.60  fof(f36,plain,(
% 1.93/0.60    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f21])).
% 1.93/0.60  fof(f21,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.93/0.60  % SZS output end Proof for theBenchmark
% 1.93/0.60  % (9462)------------------------------
% 1.93/0.60  % (9462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.60  % (9462)Termination reason: Refutation
% 1.93/0.60  
% 1.93/0.60  % (9462)Memory used [KB]: 2686
% 1.93/0.60  % (9462)Time elapsed: 0.198 s
% 1.93/0.60  % (9462)------------------------------
% 1.93/0.60  % (9462)------------------------------
% 1.93/0.60  % (9452)Success in time 0.258 s
%------------------------------------------------------------------------------
