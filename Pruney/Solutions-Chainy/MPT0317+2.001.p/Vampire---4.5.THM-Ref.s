%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 121 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   19
%              Number of atoms          :  165 ( 385 expanded)
%              Number of equality atoms :   62 ( 152 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(subsumption_resolution,[],[f410,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f410,plain,(
    ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f409,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f409,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f395,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f395,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f392,f389])).

fof(f389,plain,(
    sK1 = sK3 ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,
    ( sK1 = sK3
    | sK1 = sK3 ),
    inference(equality_resolution,[],[f382])).

fof(f382,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK3)
      | sK1 = X0
      | sK1 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK3)
      | sK1 = X0
      | sK1 = X0
      | sK1 = sK3 ) ),
    inference(superposition,[],[f161,f53])).

fof(f161,plain,(
    ! [X2,X3] :
      ( k1_tarski(sK3) != k2_xboole_0(k1_tarski(X2),k1_tarski(X3))
      | sK1 = X2
      | sK1 = X3
      | sK1 = sK3 ) ),
    inference(superposition,[],[f56,f104])).

fof(f104,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (31009)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f70,plain,
    ( r2_hidden(sK1,k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f31,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))
    | sK1 = sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK1 != sK3
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | ~ r2_hidden(sK0,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & r2_hidden(sK0,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

% (31031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_xboole_0(k1_tarski(X2),k1_tarski(X3))
      | X0 = X2
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f52,f35,f35])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X0 = X2
      | k2_tarski(X0,X1) != k2_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( X0 = X3
      | X0 = X2
      | k2_tarski(X0,X1) != k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f392,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(trivial_inequality_removal,[],[f391])).

fof(f391,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f83,f389])).

fof(f83,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | sK1 != sK3 ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f60,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f30,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK1,k1_tarski(sK3))
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))
    | sK1 != sK3 ),
    inference(subsumption_resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f32,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31013)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (31007)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (31008)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31003)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (31013)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (31016)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (31024)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (31005)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (31026)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (31032)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31017)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (31022)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (31032)Refutation not found, incomplete strategy% (31032)------------------------------
% 0.21/0.53  % (31032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31015)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (31014)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.53  % (31011)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.53  % (31025)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f411,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(subsumption_resolution,[],[f410,f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(flattening,[],[f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f410,plain,(
% 1.34/0.53    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK1))),
% 1.34/0.53    inference(forward_demodulation,[],[f409,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f33,f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.53  fof(f409,plain,(
% 1.34/0.53    ~r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1))),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f395,f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 1.34/0.53  fof(f395,plain,(
% 1.34/0.53    ~r2_hidden(sK1,k1_tarski(sK1))),
% 1.34/0.53    inference(forward_demodulation,[],[f392,f389])).
% 1.34/0.53  fof(f389,plain,(
% 1.34/0.53    sK1 = sK3),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f388])).
% 1.34/0.53  fof(f388,plain,(
% 1.34/0.53    sK1 = sK3 | sK1 = sK3),
% 1.34/0.53    inference(equality_resolution,[],[f382])).
% 1.34/0.53  fof(f382,plain,(
% 1.34/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK3) | sK1 = X0 | sK1 = sK3) )),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f376])).
% 1.34/0.53  fof(f376,plain,(
% 1.34/0.53    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK3) | sK1 = X0 | sK1 = X0 | sK1 = sK3) )),
% 1.34/0.53    inference(superposition,[],[f161,f53])).
% 1.34/0.53  fof(f161,plain,(
% 1.34/0.53    ( ! [X2,X3] : (k1_tarski(sK3) != k2_xboole_0(k1_tarski(X2),k1_tarski(X3)) | sK1 = X2 | sK1 = X3 | sK1 = sK3) )),
% 1.34/0.53    inference(superposition,[],[f56,f104])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    k1_tarski(sK3) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK3)) | sK1 = sK3),
% 1.34/0.53    inference(resolution,[],[f70,f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  % (31009)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    r2_hidden(sK1,k1_tarski(sK3)) | sK1 = sK3),
% 1.34/0.53    inference(resolution,[],[f31,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(flattening,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(nnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) | sK1 = sK3),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    (sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.34/0.53    inference(flattening,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.34/0.53    inference(nnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.34/0.53    inference(ennf_transformation,[],[f14])).
% 1.34/0.53  % (31031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  fof(f14,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.34/0.53    inference(negated_conjecture,[],[f13])).
% 1.34/0.53  fof(f13,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_xboole_0(k1_tarski(X2),k1_tarski(X3)) | X0 = X2 | X0 = X3) )),
% 1.34/0.53    inference(definition_unfolding,[],[f52,f35,f35])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (X0 = X3 | X0 = X2 | k2_tarski(X0,X1) != k2_tarski(X2,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (X0 = X3 | X0 = X2 | k2_tarski(X0,X1) != k2_tarski(X2,X3))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).
% 1.34/0.53  fof(f392,plain,(
% 1.34/0.53    ~r2_hidden(sK1,k1_tarski(sK3))),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f391])).
% 1.34/0.53  fof(f391,plain,(
% 1.34/0.53    sK1 != sK1 | ~r2_hidden(sK1,k1_tarski(sK3))),
% 1.34/0.53    inference(backward_demodulation,[],[f83,f389])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    ~r2_hidden(sK1,k1_tarski(sK3)) | sK1 != sK3),
% 1.34/0.53    inference(subsumption_resolution,[],[f81,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    r2_hidden(sK0,sK2)),
% 1.34/0.53    inference(subsumption_resolution,[],[f30,f49])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    sK1 != sK3 | ~r2_hidden(sK1,k1_tarski(sK3)) | ~r2_hidden(sK0,sK2)),
% 1.34/0.53    inference(resolution,[],[f59,f51])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) | sK1 != sK3),
% 1.34/0.53    inference(subsumption_resolution,[],[f32,f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(flattening,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(nnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (31013)------------------------------
% 1.34/0.53  % (31013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (31013)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (31013)Memory used [KB]: 6524
% 1.34/0.53  % (31013)Time elapsed: 0.106 s
% 1.34/0.53  % (31013)------------------------------
% 1.34/0.53  % (31013)------------------------------
% 1.34/0.53  % (31001)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  % (30998)Success in time 0.173 s
%------------------------------------------------------------------------------
