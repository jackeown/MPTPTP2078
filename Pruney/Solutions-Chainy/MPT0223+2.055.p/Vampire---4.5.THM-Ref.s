%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:58 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   57 (  68 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 ( 215 expanded)
%              Number of equality atoms :  150 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f33])).

% (20573)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f33,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f160,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f157,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f157,plain,(
    r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f73,f148])).

fof(f148,plain,(
    k1_tarski(sK1) = k2_tarski(sK1,sK0) ),
    inference(superposition,[],[f147,f82])).

fof(f82,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f80,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f40,f78])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f75,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f76,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f39,f32])).

fof(f32,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f147,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f142,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f142,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f106,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f106,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f101,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f73,plain,(
    ! [X4,X5] : r2_hidden(X5,k2_tarski(X4,X5)) ),
    inference(superposition,[],[f64,f38])).

fof(f64,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:27:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (1212841984)
% 0.22/0.37  ipcrm: permission denied for id (1214939137)
% 0.22/0.37  ipcrm: permission denied for id (1215004675)
% 0.22/0.38  ipcrm: permission denied for id (1215070213)
% 0.22/0.38  ipcrm: permission denied for id (1215102982)
% 0.22/0.38  ipcrm: permission denied for id (1213005832)
% 0.22/0.38  ipcrm: permission denied for id (1215201290)
% 0.22/0.38  ipcrm: permission denied for id (1215234059)
% 0.22/0.38  ipcrm: permission denied for id (1213071372)
% 0.22/0.39  ipcrm: permission denied for id (1215266829)
% 0.22/0.39  ipcrm: permission denied for id (1213235216)
% 0.22/0.39  ipcrm: permission denied for id (1215365137)
% 0.22/0.39  ipcrm: permission denied for id (1215397906)
% 0.22/0.39  ipcrm: permission denied for id (1213300756)
% 0.22/0.40  ipcrm: permission denied for id (1215496214)
% 0.22/0.40  ipcrm: permission denied for id (1215528983)
% 0.22/0.40  ipcrm: permission denied for id (1215561752)
% 0.22/0.40  ipcrm: permission denied for id (1215692827)
% 0.22/0.40  ipcrm: permission denied for id (1215725596)
% 0.22/0.41  ipcrm: permission denied for id (1213464607)
% 0.22/0.41  ipcrm: permission denied for id (1215823904)
% 0.22/0.41  ipcrm: permission denied for id (1213530145)
% 0.22/0.41  ipcrm: permission denied for id (1213562914)
% 0.22/0.41  ipcrm: permission denied for id (1215856675)
% 0.22/0.41  ipcrm: permission denied for id (1213628453)
% 0.22/0.41  ipcrm: permission denied for id (1213661222)
% 0.22/0.42  ipcrm: permission denied for id (1213726760)
% 0.22/0.42  ipcrm: permission denied for id (1215954985)
% 0.22/0.42  ipcrm: permission denied for id (1215987754)
% 0.22/0.42  ipcrm: permission denied for id (1213792300)
% 0.22/0.42  ipcrm: permission denied for id (1216053293)
% 0.22/0.42  ipcrm: permission denied for id (1216086062)
% 0.22/0.42  ipcrm: permission denied for id (1216118831)
% 0.22/0.42  ipcrm: permission denied for id (1216151600)
% 0.22/0.43  ipcrm: permission denied for id (1216217138)
% 0.22/0.43  ipcrm: permission denied for id (1213857843)
% 0.22/0.43  ipcrm: permission denied for id (1216249908)
% 0.22/0.43  ipcrm: permission denied for id (1216315446)
% 0.22/0.44  ipcrm: permission denied for id (1216479291)
% 0.22/0.44  ipcrm: permission denied for id (1216610367)
% 0.22/0.44  ipcrm: permission denied for id (1216643136)
% 0.22/0.44  ipcrm: permission denied for id (1216708674)
% 0.22/0.45  ipcrm: permission denied for id (1214087235)
% 0.22/0.45  ipcrm: permission denied for id (1214120005)
% 0.22/0.45  ipcrm: permission denied for id (1216806983)
% 0.22/0.45  ipcrm: permission denied for id (1216839752)
% 0.22/0.45  ipcrm: permission denied for id (1214185545)
% 0.22/0.45  ipcrm: permission denied for id (1216872522)
% 0.22/0.46  ipcrm: permission denied for id (1216905291)
% 0.22/0.46  ipcrm: permission denied for id (1214218320)
% 0.22/0.46  ipcrm: permission denied for id (1217069137)
% 0.22/0.46  ipcrm: permission denied for id (1217101906)
% 0.22/0.46  ipcrm: permission denied for id (1214251091)
% 0.22/0.47  ipcrm: permission denied for id (1214283860)
% 0.22/0.47  ipcrm: permission denied for id (1217134677)
% 0.22/0.47  ipcrm: permission denied for id (1214349398)
% 0.22/0.47  ipcrm: permission denied for id (1217167447)
% 0.22/0.47  ipcrm: permission denied for id (1214382169)
% 0.22/0.47  ipcrm: permission denied for id (1217232986)
% 0.22/0.47  ipcrm: permission denied for id (1214414941)
% 0.22/0.48  ipcrm: permission denied for id (1214447710)
% 0.22/0.48  ipcrm: permission denied for id (1217364064)
% 0.22/0.48  ipcrm: permission denied for id (1217527908)
% 0.22/0.49  ipcrm: permission denied for id (1217626215)
% 0.22/0.49  ipcrm: permission denied for id (1217658984)
% 0.22/0.49  ipcrm: permission denied for id (1214546025)
% 0.22/0.49  ipcrm: permission denied for id (1214578794)
% 0.22/0.49  ipcrm: permission denied for id (1217724524)
% 0.22/0.49  ipcrm: permission denied for id (1217757293)
% 0.22/0.50  ipcrm: permission denied for id (1217888369)
% 0.22/0.50  ipcrm: permission denied for id (1217953907)
% 0.22/0.50  ipcrm: permission denied for id (1217986676)
% 0.22/0.50  ipcrm: permission denied for id (1218019445)
% 0.22/0.50  ipcrm: permission denied for id (1214677111)
% 0.22/0.51  ipcrm: permission denied for id (1218084984)
% 0.22/0.51  ipcrm: permission denied for id (1214742649)
% 0.22/0.51  ipcrm: permission denied for id (1214775418)
% 0.22/0.51  ipcrm: permission denied for id (1218150524)
% 0.22/0.51  ipcrm: permission denied for id (1218183293)
% 0.22/0.51  ipcrm: permission denied for id (1218216062)
% 0.22/0.51  ipcrm: permission denied for id (1218248831)
% 0.87/0.63  % (20571)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.87/0.64  % (20578)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.87/0.65  % (20575)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.87/0.66  % (20570)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.87/0.66  % (20569)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.87/0.66  % (20592)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.87/0.66  % (20574)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.87/0.66  % (20578)Refutation found. Thanks to Tanya!
% 0.87/0.66  % SZS status Theorem for theBenchmark
% 0.87/0.66  % SZS output start Proof for theBenchmark
% 0.87/0.66  fof(f161,plain,(
% 0.87/0.66    $false),
% 0.87/0.66    inference(subsumption_resolution,[],[f160,f33])).
% 0.87/0.66  % (20573)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.87/0.66  fof(f33,plain,(
% 0.87/0.66    sK0 != sK1),
% 0.87/0.66    inference(cnf_transformation,[],[f22])).
% 0.87/0.66  fof(f22,plain,(
% 0.87/0.66    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.87/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.87/0.66  fof(f21,plain,(
% 0.87/0.66    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.87/0.66    introduced(choice_axiom,[])).
% 0.87/0.66  fof(f19,plain,(
% 0.87/0.66    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.87/0.66    inference(ennf_transformation,[],[f18])).
% 0.87/0.66  fof(f18,negated_conjecture,(
% 0.87/0.66    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.87/0.66    inference(negated_conjecture,[],[f17])).
% 0.87/0.66  fof(f17,conjecture,(
% 0.87/0.66    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.87/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.87/0.66  fof(f160,plain,(
% 0.87/0.66    sK0 = sK1),
% 0.87/0.66    inference(resolution,[],[f157,f62])).
% 0.87/0.66  fof(f62,plain,(
% 0.87/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.87/0.66    inference(equality_resolution,[],[f41])).
% 0.87/0.66  fof(f41,plain,(
% 0.87/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.87/0.66    inference(cnf_transformation,[],[f26])).
% 0.87/0.67  fof(f26,plain,(
% 0.87/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.87/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.87/0.67  fof(f25,plain,(
% 0.87/0.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.87/0.67    introduced(choice_axiom,[])).
% 0.87/0.67  fof(f24,plain,(
% 0.87/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.87/0.67    inference(rectify,[],[f23])).
% 0.87/0.67  fof(f23,plain,(
% 0.87/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.87/0.67    inference(nnf_transformation,[],[f7])).
% 0.87/0.67  fof(f7,axiom,(
% 0.87/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.87/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.87/0.67  fof(f157,plain,(
% 0.87/0.67    r2_hidden(sK0,k1_tarski(sK1))),
% 0.87/0.67    inference(superposition,[],[f73,f148])).
% 0.87/0.67  fof(f148,plain,(
% 0.87/0.67    k1_tarski(sK1) = k2_tarski(sK1,sK0)),
% 0.87/0.67    inference(superposition,[],[f147,f82])).
% 0.87/0.67  fof(f82,plain,(
% 0.87/0.67    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.87/0.67    inference(forward_demodulation,[],[f80,f34])).
% 0.87/0.67  fof(f34,plain,(
% 0.87/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.87/0.67    inference(cnf_transformation,[],[f4])).
% 0.87/0.67  fof(f4,axiom,(
% 0.87/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.87/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.87/0.67  fof(f80,plain,(
% 0.87/0.67    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 0.87/0.67    inference(superposition,[],[f40,f78])).
% 0.87/0.67  fof(f78,plain,(
% 0.87/0.67    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.87/0.67    inference(backward_demodulation,[],[f75,f77])).
% 0.87/0.67  fof(f77,plain,(
% 0.87/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.87/0.67    inference(forward_demodulation,[],[f76,f37])).
% 0.87/0.67  fof(f37,plain,(
% 0.87/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.87/0.67    inference(cnf_transformation,[],[f3])).
% 0.87/0.67  fof(f3,axiom,(
% 0.87/0.67    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.87/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.87/0.67  fof(f76,plain,(
% 0.87/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0)) )),
% 0.87/0.67    inference(superposition,[],[f39,f36])).
% 0.87/0.67  fof(f36,plain,(
% 0.87/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.87/0.67    inference(cnf_transformation,[],[f2])).
% 0.87/0.67  fof(f2,axiom,(
% 0.87/0.67    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.87/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.87/0.67  fof(f39,plain,(
% 0.87/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.87/0.67    inference(cnf_transformation,[],[f1])).
% 0.87/0.67  fof(f1,axiom,(
% 0.87/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.67  fof(f75,plain,(
% 1.34/0.67    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.34/0.67    inference(superposition,[],[f39,f32])).
% 1.34/0.67  fof(f32,plain,(
% 1.34/0.67    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.34/0.67    inference(cnf_transformation,[],[f22])).
% 1.34/0.67  fof(f40,plain,(
% 1.34/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.67    inference(cnf_transformation,[],[f5])).
% 1.34/0.67  fof(f5,axiom,(
% 1.34/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.34/0.67  fof(f147,plain,(
% 1.34/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.67    inference(forward_demodulation,[],[f142,f38])).
% 1.34/0.67  fof(f38,plain,(
% 1.34/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.67    inference(cnf_transformation,[],[f10])).
% 1.34/0.67  fof(f10,axiom,(
% 1.34/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.67  fof(f142,plain,(
% 1.34/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.67    inference(superposition,[],[f106,f35])).
% 1.34/0.67  fof(f35,plain,(
% 1.34/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.67    inference(cnf_transformation,[],[f9])).
% 1.34/0.67  fof(f9,axiom,(
% 1.34/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.67  fof(f106,plain,(
% 1.34/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.34/0.67    inference(forward_demodulation,[],[f101,f46])).
% 1.34/0.67  fof(f46,plain,(
% 1.34/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.34/0.67    inference(cnf_transformation,[],[f11])).
% 1.34/0.67  fof(f11,axiom,(
% 1.34/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.67  fof(f101,plain,(
% 1.34/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.34/0.67    inference(superposition,[],[f48,f38])).
% 1.34/0.67  fof(f48,plain,(
% 1.34/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.34/0.67    inference(cnf_transformation,[],[f8])).
% 1.34/0.67  fof(f8,axiom,(
% 1.34/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.34/0.67  fof(f73,plain,(
% 1.34/0.67    ( ! [X4,X5] : (r2_hidden(X5,k2_tarski(X4,X5))) )),
% 1.34/0.67    inference(superposition,[],[f64,f38])).
% 1.34/0.67  fof(f64,plain,(
% 1.34/0.67    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.34/0.67    inference(equality_resolution,[],[f63])).
% 1.34/0.67  fof(f63,plain,(
% 1.34/0.67    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.34/0.67    inference(equality_resolution,[],[f52])).
% 1.34/0.67  fof(f52,plain,(
% 1.34/0.67    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.34/0.67    inference(cnf_transformation,[],[f31])).
% 1.34/0.67  fof(f31,plain,(
% 1.34/0.67    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.34/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.34/0.67  fof(f30,plain,(
% 1.34/0.67    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.34/0.67    introduced(choice_axiom,[])).
% 1.34/0.67  fof(f29,plain,(
% 1.34/0.67    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.34/0.67    inference(rectify,[],[f28])).
% 1.34/0.67  fof(f28,plain,(
% 1.34/0.67    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.34/0.67    inference(flattening,[],[f27])).
% 1.34/0.67  fof(f27,plain,(
% 1.34/0.67    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.34/0.67    inference(nnf_transformation,[],[f20])).
% 1.34/0.67  fof(f20,plain,(
% 1.34/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.34/0.67    inference(ennf_transformation,[],[f6])).
% 1.34/0.67  fof(f6,axiom,(
% 1.34/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.34/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.34/0.67  % SZS output end Proof for theBenchmark
% 1.34/0.67  % (20578)------------------------------
% 1.34/0.67  % (20578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.67  % (20578)Termination reason: Refutation
% 1.34/0.67  
% 1.34/0.67  % (20578)Memory used [KB]: 1791
% 1.34/0.67  % (20578)Time elapsed: 0.109 s
% 1.34/0.67  % (20578)------------------------------
% 1.34/0.67  % (20578)------------------------------
% 1.34/0.67  % (20433)Success in time 0.295 s
%------------------------------------------------------------------------------
