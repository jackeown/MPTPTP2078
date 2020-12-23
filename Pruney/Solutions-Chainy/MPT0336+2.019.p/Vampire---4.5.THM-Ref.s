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
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   19
%              Number of atoms          :  181 ( 383 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f902,plain,(
    $false ),
    inference(subsumption_resolution,[],[f901,f38])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f29])).

fof(f29,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f901,plain,(
    ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f887,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f887,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f871,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f871,plain,(
    r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f849,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f849,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f808,f88])).

fof(f88,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(X8,k3_xboole_0(X7,X6))
      | ~ r1_xboole_0(X8,X6) ) ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f808,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f777,f52])).

fof(f777,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f776,f42])).

fof(f776,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f768,f405])).

fof(f405,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f387,f52])).

fof(f387,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f386,f38])).

fof(f386,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f377,f72])).

fof(f72,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f377,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,(
    ! [X24,X23,X22] :
      ( r1_xboole_0(X22,k2_xboole_0(X23,X24))
      | k1_xboole_0 != k3_xboole_0(X22,X24)
      | ~ r1_xboole_0(X22,X23) ) ),
    inference(superposition,[],[f54,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f768,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f577,f341])).

fof(f341,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f106,f109])).

fof(f109,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f106,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X4,X5),X6)
      | ~ r1_xboole_0(X6,k3_xboole_0(X4,X5))
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f46,f50])).

fof(f577,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(X0,k1_tarski(sK3)) ) ),
    inference(resolution,[],[f157,f36])).

fof(f36,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,(
    ! [X19,X17,X18] :
      ( ~ r1_tarski(X18,X17)
      | ~ r1_xboole_0(X19,X17)
      | r1_xboole_0(X19,X18) ) ),
    inference(superposition,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26042)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (26032)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (26035)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (26038)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (26027)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (26039)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (26040)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (26030)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (26029)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (26041)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (26033)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (26026)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (26037)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (26031)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (26025)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (26028)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (26034)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (26036)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (26028)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f902,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f901,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    r1_xboole_0(sK2,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.53  fof(f901,plain,(
% 0.21/0.53    ~r1_xboole_0(sK2,sK1)),
% 0.21/0.53    inference(resolution,[],[f887,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f887,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f871,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f50,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    r2_hidden(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f871,plain,(
% 0.21/0.53    r2_hidden(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f849,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f57,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.53  fof(f849,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.21/0.53    inference(resolution,[],[f808,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (r1_xboole_0(X8,k3_xboole_0(X7,X6)) | ~r1_xboole_0(X8,X6)) )),
% 0.21/0.53    inference(superposition,[],[f58,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.21/0.53  fof(f808,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f777,f52])).
% 0.21/0.53  fof(f777,plain,(
% 0.21/0.53    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.53    inference(forward_demodulation,[],[f776,f42])).
% 0.21/0.53  fof(f776,plain,(
% 0.21/0.53    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f768,f405])).
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f387,f52])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f386,f38])).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f381])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 0.21/0.53    inference(superposition,[],[f377,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) )),
% 0.21/0.53    inference(superposition,[],[f53,f42])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f132,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f52,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X24,X23,X22] : (r1_xboole_0(X22,k2_xboole_0(X23,X24)) | k1_xboole_0 != k3_xboole_0(X22,X24) | ~r1_xboole_0(X22,X23)) )),
% 0.21/0.53    inference(superposition,[],[f54,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f768,plain,(
% 0.21/0.53    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) | r1_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f577,f341])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f338])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(resolution,[],[f106,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 0.21/0.53    inference(superposition,[],[f46,f42])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X4,X5),X6) | ~r1_xboole_0(X6,k3_xboole_0(X4,X5)) | r1_xboole_0(X4,X5)) )),
% 0.21/0.53    inference(resolution,[],[f46,f50])).
% 0.21/0.53  fof(f577,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(X0,k1_tarski(sK3))) )),
% 0.21/0.53    inference(resolution,[],[f157,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ( ! [X19,X17,X18] : (~r1_tarski(X18,X17) | ~r1_xboole_0(X19,X17) | r1_xboole_0(X19,X18)) )),
% 0.21/0.53    inference(superposition,[],[f58,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.21/0.53    inference(superposition,[],[f51,f42])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26028)------------------------------
% 0.21/0.53  % (26028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26028)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26028)Memory used [KB]: 1918
% 0.21/0.53  % (26028)Time elapsed: 0.094 s
% 0.21/0.53  % (26028)------------------------------
% 0.21/0.53  % (26028)------------------------------
% 0.21/0.54  % (26024)Success in time 0.178 s
%------------------------------------------------------------------------------
