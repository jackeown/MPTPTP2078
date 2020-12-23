%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  84 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  164 ( 259 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f82,f30,f29,f122,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f122,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f78,f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f51,f68])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f35,f37])).

% (3219)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (3217)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (3227)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (3230)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (3229)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (3218)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (3226)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (3238)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (3222)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (3225)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (3231)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (3245)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (3243)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (3237)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (3236)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f78,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f29,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f61,f62])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (3220)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (3220)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f28,f82,f30,f29,f122,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | X0 = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f78,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X2) | ~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 0.21/0.52    inference(superposition,[],[f51,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.21/0.52    inference(superposition,[],[f50,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.52  % (3219)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (3217)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (3227)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (3230)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (3229)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (3218)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3226)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (3238)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (3222)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3225)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (3231)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (3245)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3243)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3237)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (3236)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f37])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f62,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f57,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),sK0) & v1_relat_1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & ! [X2,X1] : ~r2_hidden(k4_tarski(X1,X2),sK0) & v1_relat_1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : ((k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0)) & v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f61,f62])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f28,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (3220)------------------------------
% 0.21/0.54  % (3220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3220)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (3220)Memory used [KB]: 1791
% 0.21/0.54  % (3220)Time elapsed: 0.100 s
% 0.21/0.54  % (3220)------------------------------
% 0.21/0.54  % (3220)------------------------------
% 0.21/0.54  % (3224)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.54  % (3215)Success in time 0.177 s
%------------------------------------------------------------------------------
