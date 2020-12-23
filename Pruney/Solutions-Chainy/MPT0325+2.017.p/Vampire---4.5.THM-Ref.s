%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 431 expanded)
%              Number of leaves         :   13 ( 114 expanded)
%              Depth                    :   20
%              Number of atoms          :  166 (1287 expanded)
%              Number of equality atoms :   86 ( 458 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5629,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5546,f3025])).

fof(f3025,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f30,f2953])).

fof(f2953,plain,(
    r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f44,f2919])).

fof(f2919,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(equality_resolution,[],[f2897])).

fof(f2897,plain,(
    ! [X33,X32] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33)
      | k3_xboole_0(sK0,sK2) = X32 ) ),
    inference(subsumption_resolution,[],[f2896,f204])).

fof(f204,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f203,f29])).

fof(f29,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f203,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f197,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f197,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 != k3_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f177,f51])).

fof(f51,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f177,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ r2_hidden(X14,k3_xboole_0(k2_zfmisc_1(X12,X15),k2_zfmisc_1(X13,X16)))
      | k1_xboole_0 != k3_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f100,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 != k3_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f2896,plain,(
    ! [X33,X32] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | k3_xboole_0(sK0,sK2) = X32 ) ),
    inference(subsumption_resolution,[],[f2878,f232])).

fof(f232,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f231,f29])).

fof(f231,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f225,f38])).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 != k3_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f181,f51])).

fof(f181,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ r2_hidden(X14,k3_xboole_0(k2_zfmisc_1(X15,X12),k2_zfmisc_1(X16,X13)))
      | k1_xboole_0 != k3_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f101,f43])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 != k3_xboole_0(X1,X3) ) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2878,plain,(
    ! [X33,X32] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | k3_xboole_0(sK0,sK2) = X32 ) ),
    inference(superposition,[],[f982,f51])).

fof(f982,plain,(
    ! [X23,X21,X19,X22,X20,X18] :
      ( k3_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) != k2_zfmisc_1(X22,X23)
      | k1_xboole_0 = k3_xboole_0(X20,X21)
      | k1_xboole_0 = k3_xboole_0(X18,X19)
      | k3_xboole_0(X18,X19) = X22 ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f30,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f5546,plain,(
    r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f44,f5475])).

fof(f5475,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[],[f3425])).

fof(f3425,plain,(
    ! [X6,X5] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6)
      | k3_xboole_0(sK1,sK3) = X6 ) ),
    inference(subsumption_resolution,[],[f3424,f2948])).

fof(f2948,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f204,f2919])).

fof(f3424,plain,(
    ! [X6,X5] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6)
      | k1_xboole_0 = sK0
      | k3_xboole_0(sK1,sK3) = X6 ) ),
    inference(subsumption_resolution,[],[f3367,f232])).

fof(f3367,plain,(
    ! [X6,X5] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3)
      | k1_xboole_0 = sK0
      | k3_xboole_0(sK1,sK3) = X6 ) ),
    inference(superposition,[],[f32,f3216])).

fof(f3216,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f2949,f51])).

fof(f2949,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f2919])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:52:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.44  % (9453)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (9445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (9446)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.48  % (9470)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.48  % (9461)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.48  % (9454)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.49  % (9444)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (9462)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (9463)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (9464)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (9442)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (9443)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (9455)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (9441)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (9456)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (9447)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (9467)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (9469)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (9463)Refutation not found, incomplete strategy% (9463)------------------------------
% 0.19/0.52  % (9463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (9463)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (9463)Memory used [KB]: 10618
% 0.19/0.52  % (9463)Time elapsed: 0.098 s
% 0.19/0.52  % (9463)------------------------------
% 0.19/0.52  % (9463)------------------------------
% 0.19/0.52  % (9468)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (9466)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (9458)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (9458)Refutation not found, incomplete strategy% (9458)------------------------------
% 0.19/0.53  % (9458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9458)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9458)Memory used [KB]: 10618
% 0.19/0.53  % (9458)Time elapsed: 0.140 s
% 0.19/0.53  % (9458)------------------------------
% 0.19/0.53  % (9458)------------------------------
% 0.19/0.53  % (9460)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (9459)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (9448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (9450)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (9452)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (9451)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (9449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.55  % (9456)Refutation not found, incomplete strategy% (9456)------------------------------
% 0.19/0.55  % (9456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (9456)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (9456)Memory used [KB]: 6140
% 0.19/0.55  % (9456)Time elapsed: 0.159 s
% 0.19/0.55  % (9456)------------------------------
% 0.19/0.55  % (9456)------------------------------
% 0.19/0.55  % (9457)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.57  % (9465)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.24/0.65  % (9479)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.24/0.66  % (9482)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.24/0.66  % (9491)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.84/0.76  % (9446)Refutation found. Thanks to Tanya!
% 2.84/0.76  % SZS status Theorem for theBenchmark
% 2.84/0.76  % SZS output start Proof for theBenchmark
% 2.84/0.76  fof(f5629,plain,(
% 2.84/0.76    $false),
% 2.84/0.76    inference(subsumption_resolution,[],[f5546,f3025])).
% 2.84/0.76  fof(f3025,plain,(
% 2.84/0.76    ~r1_tarski(sK1,sK3)),
% 2.84/0.76    inference(subsumption_resolution,[],[f30,f2953])).
% 2.84/0.76  fof(f2953,plain,(
% 2.84/0.76    r1_tarski(sK0,sK2)),
% 2.84/0.76    inference(superposition,[],[f44,f2919])).
% 2.84/0.76  fof(f2919,plain,(
% 2.84/0.76    sK0 = k3_xboole_0(sK0,sK2)),
% 2.84/0.76    inference(equality_resolution,[],[f2897])).
% 2.84/0.76  fof(f2897,plain,(
% 2.84/0.76    ( ! [X33,X32] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33) | k3_xboole_0(sK0,sK2) = X32) )),
% 2.84/0.76    inference(subsumption_resolution,[],[f2896,f204])).
% 2.84/0.76  fof(f204,plain,(
% 2.84/0.76    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 2.84/0.76    inference(subsumption_resolution,[],[f203,f29])).
% 2.84/0.76  fof(f29,plain,(
% 2.84/0.76    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.84/0.76    inference(cnf_transformation,[],[f22])).
% 2.84/0.76  fof(f22,plain,(
% 2.84/0.76    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.84/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21])).
% 2.84/0.76  fof(f21,plain,(
% 2.84/0.76    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 2.84/0.76    introduced(choice_axiom,[])).
% 2.84/0.76  fof(f14,plain,(
% 2.84/0.76    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.84/0.76    inference(flattening,[],[f13])).
% 2.84/0.76  fof(f13,plain,(
% 2.84/0.76    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.84/0.76    inference(ennf_transformation,[],[f11])).
% 2.84/0.76  fof(f11,negated_conjecture,(
% 2.84/0.76    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.84/0.76    inference(negated_conjecture,[],[f10])).
% 2.84/0.76  fof(f10,conjecture,(
% 2.84/0.76    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.84/0.76  fof(f203,plain,(
% 2.84/0.76    k1_xboole_0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.84/0.76    inference(resolution,[],[f197,f38])).
% 2.84/0.76  fof(f38,plain,(
% 2.84/0.76    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.84/0.76    inference(cnf_transformation,[],[f25])).
% 2.84/0.76  fof(f25,plain,(
% 2.84/0.76    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.84/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 2.84/0.76  fof(f24,plain,(
% 2.84/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.84/0.76    introduced(choice_axiom,[])).
% 2.84/0.76  fof(f18,plain,(
% 2.84/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.84/0.76    inference(ennf_transformation,[],[f4])).
% 2.84/0.76  fof(f4,axiom,(
% 2.84/0.76    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.84/0.76  fof(f197,plain,(
% 2.84/0.76    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK0,sK2)) )),
% 2.84/0.76    inference(superposition,[],[f177,f51])).
% 2.84/0.76  fof(f51,plain,(
% 2.84/0.76    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.84/0.76    inference(resolution,[],[f36,f28])).
% 2.84/0.76  fof(f28,plain,(
% 2.84/0.76    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.84/0.76    inference(cnf_transformation,[],[f22])).
% 2.84/0.76  fof(f36,plain,(
% 2.84/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.84/0.76    inference(cnf_transformation,[],[f17])).
% 2.84/0.76  fof(f17,plain,(
% 2.84/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.84/0.76    inference(ennf_transformation,[],[f6])).
% 2.84/0.76  fof(f6,axiom,(
% 2.84/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.84/0.76  fof(f177,plain,(
% 2.84/0.76    ( ! [X14,X12,X15,X13,X16] : (~r2_hidden(X14,k3_xboole_0(k2_zfmisc_1(X12,X15),k2_zfmisc_1(X13,X16))) | k1_xboole_0 != k3_xboole_0(X12,X13)) )),
% 2.84/0.76    inference(resolution,[],[f100,f43])).
% 2.84/0.76  fof(f43,plain,(
% 2.84/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f27])).
% 2.84/0.76  fof(f27,plain,(
% 2.84/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.84/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f26])).
% 2.84/0.76  fof(f26,plain,(
% 2.84/0.76    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.84/0.76    introduced(choice_axiom,[])).
% 2.84/0.76  fof(f20,plain,(
% 2.84/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.84/0.76    inference(ennf_transformation,[],[f12])).
% 2.84/0.76  fof(f12,plain,(
% 2.84/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.84/0.76    inference(rectify,[],[f3])).
% 2.84/0.76  fof(f3,axiom,(
% 2.84/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.84/0.76  fof(f100,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 != k3_xboole_0(X0,X2)) )),
% 2.84/0.76    inference(resolution,[],[f40,f35])).
% 2.84/0.76  fof(f35,plain,(
% 2.84/0.76    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.84/0.76    inference(cnf_transformation,[],[f23])).
% 2.84/0.76  fof(f23,plain,(
% 2.84/0.76    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.84/0.76    inference(nnf_transformation,[],[f2])).
% 2.84/0.76  fof(f2,axiom,(
% 2.84/0.76    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.84/0.76  fof(f40,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f19])).
% 2.84/0.76  fof(f19,plain,(
% 2.84/0.76    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 2.84/0.76    inference(ennf_transformation,[],[f8])).
% 2.84/0.76  fof(f8,axiom,(
% 2.84/0.76    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 2.84/0.76  fof(f2896,plain,(
% 2.84/0.76    ( ! [X33,X32] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k3_xboole_0(sK0,sK2) = X32) )),
% 2.84/0.76    inference(subsumption_resolution,[],[f2878,f232])).
% 2.84/0.76  fof(f232,plain,(
% 2.84/0.76    k1_xboole_0 != k3_xboole_0(sK1,sK3)),
% 2.84/0.76    inference(subsumption_resolution,[],[f231,f29])).
% 2.84/0.76  fof(f231,plain,(
% 2.84/0.76    k1_xboole_0 != k3_xboole_0(sK1,sK3) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.84/0.76    inference(resolution,[],[f225,f38])).
% 2.84/0.76  fof(f225,plain,(
% 2.84/0.76    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK1,sK3)) )),
% 2.84/0.76    inference(superposition,[],[f181,f51])).
% 2.84/0.76  fof(f181,plain,(
% 2.84/0.76    ( ! [X14,X12,X15,X13,X16] : (~r2_hidden(X14,k3_xboole_0(k2_zfmisc_1(X15,X12),k2_zfmisc_1(X16,X13))) | k1_xboole_0 != k3_xboole_0(X12,X13)) )),
% 2.84/0.76    inference(resolution,[],[f101,f43])).
% 2.84/0.76  fof(f101,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 != k3_xboole_0(X1,X3)) )),
% 2.84/0.76    inference(resolution,[],[f41,f35])).
% 2.84/0.76  fof(f41,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f19])).
% 2.84/0.76  fof(f2878,plain,(
% 2.84/0.76    ( ! [X33,X32] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X32,X33) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k3_xboole_0(sK0,sK2) = X32) )),
% 2.84/0.76    inference(superposition,[],[f982,f51])).
% 2.84/0.76  fof(f982,plain,(
% 2.84/0.76    ( ! [X23,X21,X19,X22,X20,X18] : (k3_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) != k2_zfmisc_1(X22,X23) | k1_xboole_0 = k3_xboole_0(X20,X21) | k1_xboole_0 = k3_xboole_0(X18,X19) | k3_xboole_0(X18,X19) = X22) )),
% 2.84/0.76    inference(superposition,[],[f31,f33])).
% 2.84/0.76  fof(f33,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f7])).
% 2.84/0.76  fof(f7,axiom,(
% 2.84/0.76    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.84/0.76  fof(f31,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 2.84/0.76    inference(cnf_transformation,[],[f16])).
% 2.84/0.76  fof(f16,plain,(
% 2.84/0.76    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 2.84/0.76    inference(flattening,[],[f15])).
% 2.84/0.76  fof(f15,plain,(
% 2.84/0.76    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 2.84/0.76    inference(ennf_transformation,[],[f9])).
% 2.84/0.76  fof(f9,axiom,(
% 2.84/0.76    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 2.84/0.76  fof(f44,plain,(
% 2.84/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.84/0.76    inference(superposition,[],[f39,f37])).
% 2.84/0.76  fof(f37,plain,(
% 2.84/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.84/0.76    inference(cnf_transformation,[],[f1])).
% 2.84/0.76  fof(f1,axiom,(
% 2.84/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.84/0.76  fof(f39,plain,(
% 2.84/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.84/0.76    inference(cnf_transformation,[],[f5])).
% 2.84/0.76  fof(f5,axiom,(
% 2.84/0.76    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.84/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.84/0.76  fof(f30,plain,(
% 2.84/0.76    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 2.84/0.76    inference(cnf_transformation,[],[f22])).
% 2.84/0.76  fof(f5546,plain,(
% 2.84/0.76    r1_tarski(sK1,sK3)),
% 2.84/0.76    inference(superposition,[],[f44,f5475])).
% 2.84/0.76  fof(f5475,plain,(
% 2.84/0.76    sK1 = k3_xboole_0(sK1,sK3)),
% 2.84/0.76    inference(equality_resolution,[],[f3425])).
% 2.84/0.76  fof(f3425,plain,(
% 2.84/0.76    ( ! [X6,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6) | k3_xboole_0(sK1,sK3) = X6) )),
% 2.84/0.76    inference(subsumption_resolution,[],[f3424,f2948])).
% 2.84/0.76  fof(f2948,plain,(
% 2.84/0.76    k1_xboole_0 != sK0),
% 2.84/0.76    inference(superposition,[],[f204,f2919])).
% 2.84/0.76  fof(f3424,plain,(
% 2.84/0.76    ( ! [X6,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6) | k1_xboole_0 = sK0 | k3_xboole_0(sK1,sK3) = X6) )),
% 2.84/0.76    inference(subsumption_resolution,[],[f3367,f232])).
% 2.84/0.76  fof(f3367,plain,(
% 2.84/0.76    ( ! [X6,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X5,X6) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = sK0 | k3_xboole_0(sK1,sK3) = X6) )),
% 2.84/0.76    inference(superposition,[],[f32,f3216])).
% 2.84/0.76  fof(f3216,plain,(
% 2.84/0.76    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.84/0.76    inference(superposition,[],[f2949,f51])).
% 2.84/0.76  fof(f2949,plain,(
% 2.84/0.76    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,X1))) )),
% 2.84/0.76    inference(superposition,[],[f33,f2919])).
% 2.84/0.76  fof(f32,plain,(
% 2.84/0.76    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 2.84/0.76    inference(cnf_transformation,[],[f16])).
% 2.84/0.76  % SZS output end Proof for theBenchmark
% 2.84/0.76  % (9446)------------------------------
% 2.84/0.76  % (9446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.84/0.76  % (9446)Termination reason: Refutation
% 2.84/0.76  
% 2.84/0.76  % (9446)Memory used [KB]: 9466
% 2.84/0.76  % (9446)Time elapsed: 0.377 s
% 2.84/0.76  % (9446)------------------------------
% 2.84/0.76  % (9446)------------------------------
% 2.84/0.77  % (9437)Success in time 0.417 s
%------------------------------------------------------------------------------
