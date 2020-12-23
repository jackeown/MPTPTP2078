%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  17 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(global_subsumption,[],[f9,f11])).

fof(f11,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f8,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f8,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( r2_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).

fof(f9,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (12003)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (12000)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.48  % (12011)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (12008)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (12008)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(global_subsumption,[],[f9,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ~r2_xboole_0(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f8,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1] : (r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (r2_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f4,plain,(
% 0.22/0.49    ? [X0,X1] : (r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ~(r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f2])).
% 0.22/0.49  fof(f2,conjecture,(
% 0.22/0.49    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (12008)------------------------------
% 0.22/0.49  % (12008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12008)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (12008)Memory used [KB]: 9722
% 0.22/0.49  % (12008)Time elapsed: 0.069 s
% 0.22/0.49  % (12008)------------------------------
% 0.22/0.49  % (12008)------------------------------
% 0.22/0.51  % (11998)Success in time 0.145 s
%------------------------------------------------------------------------------
