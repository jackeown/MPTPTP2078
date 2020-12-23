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
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 213 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   22
%              Number of atoms          :  200 ( 729 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f649,plain,(
    $false ),
    inference(subsumption_resolution,[],[f648,f84])).

fof(f84,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f78,f81])).

fof(f81,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f76,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f42,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f78,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f77,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f77,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f648,plain,(
    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f646,f81])).

fof(f646,plain,(
    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f136,f642])).

fof(f642,plain,(
    ! [X1] : k3_xboole_0(sK1,X1) = k3_xboole_0(sK1,k2_xboole_0(sK0,X1)) ),
    inference(resolution,[],[f638,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f638,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f633,f56])).

fof(f633,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f620,f84])).

fof(f620,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f52,f605])).

fof(f605,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f402,f591])).

fof(f591,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f509,f57])).

fof(f509,plain,(
    ! [X5] : r1_xboole_0(k3_xboole_0(X5,sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f451,f56])).

fof(f451,plain,(
    ! [X5] : r1_xboole_0(k1_tarski(sK3),k3_xboole_0(X5,sK1)) ),
    inference(resolution,[],[f417,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f417,plain,(
    ! [X1] : ~ r2_hidden(sK3,k3_xboole_0(X1,sK1)) ),
    inference(resolution,[],[f411,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f411,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(subsumption_resolution,[],[f129,f84])).

fof(f129,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(superposition,[],[f68,f75])).

fof(f75,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f42,f57])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f402,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f94,f52])).

fof(f94,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f43,f56])).

fof(f43,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6489)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (6504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (6493)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6512)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (6496)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  % (6505)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.53  % (6497)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (6501)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (6491)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.54  % (6492)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  % (6494)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.54  % (6513)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.54  % (6490)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.54  % (6511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.54  % (6503)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.54  % (6517)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (6518)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (6509)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (6514)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (6516)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (6510)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (6507)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (6515)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (6508)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (6495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.55  % (6511)Refutation not found, incomplete strategy% (6511)------------------------------
% 1.43/0.55  % (6511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (6511)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (6511)Memory used [KB]: 10746
% 1.43/0.55  % (6511)Time elapsed: 0.097 s
% 1.43/0.55  % (6511)------------------------------
% 1.43/0.55  % (6511)------------------------------
% 1.43/0.55  % (6506)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (6499)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (6502)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.55  % (6500)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (6498)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.57  % (6512)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f649,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(subsumption_resolution,[],[f648,f84])).
% 1.43/0.57  fof(f84,plain,(
% 1.43/0.57    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.43/0.57    inference(backward_demodulation,[],[f78,f81])).
% 1.43/0.57  fof(f81,plain,(
% 1.43/0.57    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.43/0.57    inference(resolution,[],[f76,f57])).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f34])).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.43/0.57    inference(nnf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.43/0.57  fof(f76,plain,(
% 1.43/0.57    r1_xboole_0(sK1,sK2)),
% 1.43/0.57    inference(resolution,[],[f42,f56])).
% 1.43/0.57  fof(f56,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f27])).
% 1.43/0.57  fof(f27,plain,(
% 1.43/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    r1_xboole_0(sK2,sK1)),
% 1.43/0.57    inference(cnf_transformation,[],[f31])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f30])).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.43/0.57    inference(flattening,[],[f22])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.43/0.57    inference(ennf_transformation,[],[f19])).
% 1.43/0.57  fof(f19,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.43/0.57    inference(negated_conjecture,[],[f18])).
% 1.43/0.57  fof(f18,conjecture,(
% 1.43/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK1,sK2))) )),
% 1.43/0.57    inference(forward_demodulation,[],[f77,f48])).
% 1.43/0.57  fof(f48,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.57  fof(f77,plain,(
% 1.43/0.57    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK2,sK1))) )),
% 1.43/0.57    inference(resolution,[],[f42,f53])).
% 1.43/0.57  fof(f53,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f33])).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).
% 1.43/0.58  fof(f32,plain,(
% 1.43/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.43/0.58    inference(ennf_transformation,[],[f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.58    inference(rectify,[],[f7])).
% 1.43/0.58  fof(f7,axiom,(
% 1.43/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.43/0.58  fof(f648,plain,(
% 1.43/0.58    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k1_xboole_0)),
% 1.43/0.58    inference(forward_demodulation,[],[f646,f81])).
% 1.43/0.58  fof(f646,plain,(
% 1.43/0.58    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK2))),
% 1.43/0.58    inference(backward_demodulation,[],[f136,f642])).
% 1.43/0.58  fof(f642,plain,(
% 1.43/0.58    ( ! [X1] : (k3_xboole_0(sK1,X1) = k3_xboole_0(sK1,k2_xboole_0(sK0,X1))) )),
% 1.43/0.58    inference(resolution,[],[f638,f60])).
% 1.43/0.58  fof(f60,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f28])).
% 1.43/0.58  fof(f28,plain,(
% 1.43/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.43/0.58  fof(f638,plain,(
% 1.43/0.58    r1_xboole_0(sK1,sK0)),
% 1.43/0.58    inference(resolution,[],[f633,f56])).
% 1.43/0.58  fof(f633,plain,(
% 1.43/0.58    r1_xboole_0(sK0,sK1)),
% 1.43/0.58    inference(subsumption_resolution,[],[f620,f84])).
% 1.43/0.58  fof(f620,plain,(
% 1.43/0.58    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | r1_xboole_0(sK0,sK1)),
% 1.43/0.58    inference(superposition,[],[f52,f605])).
% 1.43/0.58  fof(f605,plain,(
% 1.43/0.58    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.43/0.58    inference(backward_demodulation,[],[f402,f591])).
% 1.43/0.58  fof(f591,plain,(
% 1.43/0.58    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK1),k1_tarski(sK3))) )),
% 1.43/0.58    inference(resolution,[],[f509,f57])).
% 1.43/0.58  fof(f509,plain,(
% 1.43/0.58    ( ! [X5] : (r1_xboole_0(k3_xboole_0(X5,sK1),k1_tarski(sK3))) )),
% 1.43/0.58    inference(resolution,[],[f451,f56])).
% 1.43/0.58  fof(f451,plain,(
% 1.43/0.58    ( ! [X5] : (r1_xboole_0(k1_tarski(sK3),k3_xboole_0(X5,sK1))) )),
% 1.43/0.58    inference(resolution,[],[f417,f54])).
% 1.43/0.58  fof(f54,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f17])).
% 1.43/0.58  fof(f17,axiom,(
% 1.43/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.43/0.58  fof(f417,plain,(
% 1.43/0.58    ( ! [X1] : (~r2_hidden(sK3,k3_xboole_0(X1,sK1))) )),
% 1.43/0.58    inference(resolution,[],[f411,f69])).
% 1.43/0.58  fof(f69,plain,(
% 1.43/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.43/0.58    inference(equality_resolution,[],[f62])).
% 1.43/0.58  fof(f62,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.43/0.58    inference(cnf_transformation,[],[f39])).
% 1.43/0.58  fof(f39,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.43/0.58  fof(f38,plain,(
% 1.43/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f37,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(rectify,[],[f36])).
% 1.43/0.58  fof(f36,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(flattening,[],[f35])).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(nnf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.43/0.58  fof(f411,plain,(
% 1.43/0.58    ~r2_hidden(sK3,sK1)),
% 1.43/0.58    inference(resolution,[],[f133,f41])).
% 1.43/0.58  fof(f41,plain,(
% 1.43/0.58    r2_hidden(sK3,sK2)),
% 1.43/0.58    inference(cnf_transformation,[],[f31])).
% 1.43/0.58  fof(f133,plain,(
% 1.43/0.58    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK1)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f129,f84])).
% 1.43/0.58  fof(f129,plain,(
% 1.43/0.58    ( ! [X5] : (r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK1) | ~r2_hidden(X5,sK2)) )),
% 1.43/0.58    inference(superposition,[],[f68,f75])).
% 1.43/0.58  fof(f75,plain,(
% 1.43/0.58    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.43/0.58    inference(resolution,[],[f42,f57])).
% 1.43/0.58  fof(f68,plain,(
% 1.43/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.43/0.58    inference(equality_resolution,[],[f63])).
% 1.43/0.58  fof(f63,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.43/0.58    inference(cnf_transformation,[],[f39])).
% 1.43/0.58  fof(f402,plain,(
% 1.43/0.58    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.43/0.58    inference(resolution,[],[f40,f55])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f26])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.43/0.58  fof(f40,plain,(
% 1.43/0.58    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.43/0.58    inference(cnf_transformation,[],[f31])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f33])).
% 1.43/0.58  fof(f136,plain,(
% 1.43/0.58    r2_hidden(sK4(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 1.43/0.58    inference(resolution,[],[f94,f52])).
% 1.43/0.58  fof(f94,plain,(
% 1.43/0.58    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.43/0.58    inference(resolution,[],[f43,f56])).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.43/0.58    inference(cnf_transformation,[],[f31])).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (6512)------------------------------
% 1.43/0.58  % (6512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (6512)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (6512)Memory used [KB]: 2046
% 1.43/0.58  % (6512)Time elapsed: 0.141 s
% 1.43/0.58  % (6512)------------------------------
% 1.43/0.58  % (6512)------------------------------
% 1.43/0.58  % (6488)Success in time 0.218 s
%------------------------------------------------------------------------------
