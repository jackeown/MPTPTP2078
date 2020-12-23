%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 245 expanded)
%              Number of leaves         :    8 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  173 (1279 expanded)
%              Number of equality atoms :   23 ( 182 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f65])).

fof(f65,plain,(
    r2_hidden(sK3(k3_relat_1(sK0),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f64,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (12614)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f23,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k3_relat_1(X0) != k1_xboole_0
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k3_relat_1(X0) != k1_xboole_0
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k3_relat_1(X0) != k1_xboole_0
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(f61,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f39,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1,X2),X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK2(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).

fof(f16,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK2(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord1)).

fof(f36,plain,(
    r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f33,f22])).

fof(f22,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

fof(f57,plain,
    ( ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f56,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f51,f24])).

fof(f24,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK2(sK0,X1),X2),sK0)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f40,f21])).

fof(f40,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK2(sK0,X1),X2),sK0)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ~ r2_hidden(sK3(k3_relat_1(sK0),k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (12611)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (12618)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (12635)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (12610)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (12627)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (12610)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    r2_hidden(sK3(k3_relat_1(sK0),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f64,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  % (12614)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f61,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    k1_xboole_0 != k3_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X1] : ((~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0)) => (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0] : ((! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f4])).
% 0.20/0.50  fof(f4,conjecture,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f57,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(sK0,X0),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f39,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(sK0,X0),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f36,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1,X2),X2) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((! [X4] : (r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK2(X1,X2),X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X2,X1] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) => (! [X4] : (r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(sK2(X1,X2),X2)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1] : ((! [X2] : (? [X3] : (! [X4] : (r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X2)) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0)) | ~r2_wellord1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_wellord1(X1,X0) => ! [X2] : ~(! [X3] : ~(! [X4] : (r2_hidden(X4,X2) => r2_hidden(k4_tarski(X3,X4),X1)) & r2_hidden(X3,X2)) & k1_xboole_0 != X2 & r1_tarski(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord1)).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    r2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f33,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    v2_wellord1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r2_wellord1(sK0,k3_relat_1(sK0)) | ~v2_wellord1(sK0)),
% 0.20/0.50    inference(resolution,[],[f21,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0] : (r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (((r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0)) & (v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f56,f23])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f51,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))) )),
% 0.20/0.50    inference(resolution,[],[f42,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK2(sK0,X1),X2),sK0) | ~r2_hidden(X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f40,f21])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK2(sK0,X1),X2),sK0) | ~r2_hidden(X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f36,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X1,X2),X4),X1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X2 | ~r1_tarski(X2,X0) | ~r2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~r2_hidden(sK3(k3_relat_1(sK0),k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f64,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (12610)------------------------------
% 0.20/0.50  % (12610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12610)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (12610)Memory used [KB]: 1791
% 0.20/0.50  % (12610)Time elapsed: 0.109 s
% 0.20/0.50  % (12610)------------------------------
% 0.20/0.50  % (12610)------------------------------
% 0.20/0.50  % (12612)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (12618)Refutation not found, incomplete strategy% (12618)------------------------------
% 0.20/0.50  % (12618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12618)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12618)Memory used [KB]: 10618
% 0.20/0.50  % (12618)Time elapsed: 0.103 s
% 0.20/0.50  % (12618)------------------------------
% 0.20/0.50  % (12618)------------------------------
% 0.20/0.50  % (12613)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (12612)Refutation not found, incomplete strategy% (12612)------------------------------
% 0.20/0.50  % (12612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12612)Memory used [KB]: 10618
% 0.20/0.50  % (12612)Time elapsed: 0.109 s
% 0.20/0.50  % (12612)------------------------------
% 0.20/0.50  % (12612)------------------------------
% 0.20/0.51  % (12623)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (12638)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (12626)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (12634)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (12637)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (12609)Success in time 0.158 s
%------------------------------------------------------------------------------
