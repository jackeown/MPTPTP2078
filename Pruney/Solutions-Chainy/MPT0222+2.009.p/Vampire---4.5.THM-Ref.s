%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 144 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   23
%              Number of atoms          :  186 ( 435 expanded)
%              Number of equality atoms :   98 ( 218 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30196)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f553,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f552])).

fof(f552,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f23,f535])).

fof(f535,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK1 ),
    inference(superposition,[],[f46,f496])).

fof(f496,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f477])).

fof(f477,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f50,f473])).

fof(f473,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f459,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f459,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f438,f44])).

fof(f438,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK1))
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK1))
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f93,f428])).

fof(f428,plain,
    ( k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f50,f375])).

fof(f375,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f188,f372])).

fof(f372,plain,
    ( k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))
    | k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f50,f330])).

fof(f330,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))
      | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1))
      | k1_tarski(X1) = sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(resolution,[],[f136,f44])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))
      | k1_xboole_0 = sK2(k1_xboole_0,X1,k1_tarski(X0))
      | k1_tarski(X0) = sK2(k1_xboole_0,X1,k1_tarski(X0)) ) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X7,k1_tarski(X6))
      | ~ r1_tarski(X7,X5)
      | k4_xboole_0(X5,k4_xboole_0(X5,k1_tarski(X6))) = X7
      | k1_xboole_0 = sK2(X7,X5,k1_tarski(X6))
      | k1_tarski(X6) = sK2(X7,X5,k1_tarski(X6)) ) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK2(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

% (30213)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f188,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1)),k1_tarski(X0))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) ),
    inference(resolution,[],[f116,f44])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))
      | k1_xboole_0 = k4_xboole_0(sK2(k1_xboole_0,X1,k1_tarski(X0)),X1) ) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r1_tarski(X4,X2)
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X4
      | k1_xboole_0 = k4_xboole_0(sK2(X4,X2,X3),X2) ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK2(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK2(k1_xboole_0,X0,X1)
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f58,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(sK2(X2,X0,X1),X2)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK2(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (30194)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (30216)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (30221)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (30221)Refutation not found, incomplete strategy% (30221)------------------------------
% 0.20/0.51  % (30221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30216)Refutation not found, incomplete strategy% (30216)------------------------------
% 0.20/0.51  % (30216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30191)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (30203)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (30221)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30221)Memory used [KB]: 1663
% 0.20/0.52  % (30221)Time elapsed: 0.121 s
% 0.20/0.52  % (30221)------------------------------
% 0.20/0.52  % (30221)------------------------------
% 0.20/0.52  % (30216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30216)Memory used [KB]: 10618
% 0.20/0.52  % (30216)Time elapsed: 0.120 s
% 0.20/0.52  % (30216)------------------------------
% 0.20/0.52  % (30216)------------------------------
% 0.20/0.52  % (30194)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  % (30196)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  fof(f553,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f552])).
% 0.20/0.52  fof(f552,plain,(
% 0.20/0.52    sK0 != sK0),
% 0.20/0.52    inference(superposition,[],[f23,f535])).
% 0.20/0.52  fof(f535,plain,(
% 0.20/0.52    sK0 = sK1),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f508])).
% 0.20/0.52  fof(f508,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | sK0 = sK1),
% 0.20/0.52    inference(superposition,[],[f46,f496])).
% 0.20/0.52  fof(f496,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f477])).
% 0.20/0.52  fof(f477,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(superposition,[],[f50,f473])).
% 0.20/0.52  fof(f473,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(resolution,[],[f459,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.52  fof(f459,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(resolution,[],[f438,f44])).
% 0.20/0.52  fof(f438,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_tarski(sK1)) | ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f433])).
% 0.20/0.52  fof(f433,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k1_tarski(sK1)) | ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(superposition,[],[f93,f428])).
% 0.20/0.52  fof(f428,plain,(
% 0.20/0.52    k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f411])).
% 0.20/0.52  fof(f411,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(superposition,[],[f50,f375])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(superposition,[],[f188,f372])).
% 0.20/0.52  fof(f372,plain,(
% 0.20/0.52    k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f357])).
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) | k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(superposition,[],[f50,f330])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) | k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1)) | k1_tarski(X1) = sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.52    inference(resolution,[],[f136,f44])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) | k1_xboole_0 = sK2(k1_xboole_0,X1,k1_tarski(X0)) | k1_tarski(X0) = sK2(k1_xboole_0,X1,k1_tarski(X0))) )),
% 0.20/0.52    inference(resolution,[],[f61,f44])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X6,X7,X5] : (~r1_tarski(X7,k1_tarski(X6)) | ~r1_tarski(X7,X5) | k4_xboole_0(X5,k4_xboole_0(X5,k1_tarski(X6))) = X7 | k1_xboole_0 = sK2(X7,X5,k1_tarski(X6)) | k1_tarski(X6) = sK2(X7,X5,k1_tarski(X6))) )),
% 0.20/0.52    inference(resolution,[],[f41,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X2) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK2(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  % (30213)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(sK2(k1_xboole_0,k1_tarski(X0),k1_tarski(X1)),k1_tarski(X0)) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.20/0.52    inference(resolution,[],[f116,f44])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) | k1_xboole_0 = k4_xboole_0(sK2(k1_xboole_0,X1,k1_tarski(X0)),X1)) )),
% 0.20/0.52    inference(resolution,[],[f64,f44])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | ~r1_tarski(X4,X2) | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X4 | k1_xboole_0 = k4_xboole_0(sK2(X4,X2,X3),X2)) )),
% 0.20/0.52    inference(resolution,[],[f42,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X1) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f36])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK2(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != sK2(k1_xboole_0,X0,X1) | ~r1_tarski(k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(superposition,[],[f58,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(sK2(X2,X0,X1),X2) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 0.20/0.52    inference(resolution,[],[f40,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(sK2(X0,X1,X2),X0) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f36])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK2(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.52    inference(resolution,[],[f38,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f26,f36])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.52    inference(resolution,[],[f34,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (30194)------------------------------
% 0.20/0.52  % (30194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30194)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (30194)Memory used [KB]: 2046
% 0.20/0.52  % (30194)Time elapsed: 0.131 s
% 0.20/0.52  % (30194)------------------------------
% 0.20/0.52  % (30194)------------------------------
% 0.20/0.53  % (30183)Success in time 0.166 s
%------------------------------------------------------------------------------
