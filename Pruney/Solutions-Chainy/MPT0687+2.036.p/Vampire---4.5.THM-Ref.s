%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:42 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 186 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 438 expanded)
%              Number of equality atoms :   55 ( 200 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(resolution,[],[f92,f80])).

fof(f80,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f46,f78])).

fof(f78,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

% (9228)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f76,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_relat_1(sK1))
      | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(X4,X4,X4,X4,X4)) ) ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f73,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f46,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f26,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(superposition,[],[f84,f87])).

fof(f87,plain,(
    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f85,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f85,plain,(
    r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f82,f25])).

fof(f82,plain,
    ( ~ v1_relat_1(sK1)
    | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f31,f78])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)
      | ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(superposition,[],[f49,f54])).

fof(f54,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X1) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (721256449)
% 0.20/0.36  ipcrm: permission denied for id (721289218)
% 0.20/0.36  ipcrm: permission denied for id (722632707)
% 0.20/0.37  ipcrm: permission denied for id (726368260)
% 0.20/0.37  ipcrm: permission denied for id (721321989)
% 0.20/0.37  ipcrm: permission denied for id (721354758)
% 0.20/0.37  ipcrm: permission denied for id (721387527)
% 0.20/0.37  ipcrm: permission denied for id (721420297)
% 0.20/0.38  ipcrm: permission denied for id (722796556)
% 0.20/0.38  ipcrm: permission denied for id (726532110)
% 0.20/0.38  ipcrm: permission denied for id (722894863)
% 0.20/0.38  ipcrm: permission denied for id (726564880)
% 0.20/0.38  ipcrm: permission denied for id (722960401)
% 0.20/0.38  ipcrm: permission denied for id (726597650)
% 0.20/0.38  ipcrm: permission denied for id (723025939)
% 0.20/0.39  ipcrm: permission denied for id (723058708)
% 0.20/0.39  ipcrm: permission denied for id (723091477)
% 0.20/0.39  ipcrm: permission denied for id (726630422)
% 0.20/0.39  ipcrm: permission denied for id (723157015)
% 0.20/0.39  ipcrm: permission denied for id (723189784)
% 0.20/0.39  ipcrm: permission denied for id (723222553)
% 0.20/0.39  ipcrm: permission denied for id (726663194)
% 0.20/0.39  ipcrm: permission denied for id (726695963)
% 0.20/0.40  ipcrm: permission denied for id (726761501)
% 0.20/0.40  ipcrm: permission denied for id (723386398)
% 0.20/0.40  ipcrm: permission denied for id (721518623)
% 0.20/0.40  ipcrm: permission denied for id (721551392)
% 0.20/0.40  ipcrm: permission denied for id (721584161)
% 0.20/0.40  ipcrm: permission denied for id (726794274)
% 0.20/0.40  ipcrm: permission denied for id (721616931)
% 0.20/0.41  ipcrm: permission denied for id (723451940)
% 0.20/0.41  ipcrm: permission denied for id (726827045)
% 0.20/0.41  ipcrm: permission denied for id (721682470)
% 0.20/0.41  ipcrm: permission denied for id (723517479)
% 0.20/0.41  ipcrm: permission denied for id (723681323)
% 0.20/0.42  ipcrm: permission denied for id (723714092)
% 0.20/0.42  ipcrm: permission denied for id (723779629)
% 0.20/0.42  ipcrm: permission denied for id (727056430)
% 0.20/0.42  ipcrm: permission denied for id (727154737)
% 0.20/0.42  ipcrm: permission denied for id (727187506)
% 0.21/0.42  ipcrm: permission denied for id (727220275)
% 0.21/0.43  ipcrm: permission denied for id (724009012)
% 0.21/0.43  ipcrm: permission denied for id (724041781)
% 0.21/0.43  ipcrm: permission denied for id (721846326)
% 0.21/0.43  ipcrm: permission denied for id (724074551)
% 0.21/0.43  ipcrm: permission denied for id (727253048)
% 0.21/0.43  ipcrm: permission denied for id (727285817)
% 0.21/0.43  ipcrm: permission denied for id (724172858)
% 0.21/0.43  ipcrm: permission denied for id (724205627)
% 0.21/0.44  ipcrm: permission denied for id (724271165)
% 0.21/0.44  ipcrm: permission denied for id (727384127)
% 0.21/0.44  ipcrm: permission denied for id (727416896)
% 0.21/0.44  ipcrm: permission denied for id (727482434)
% 0.21/0.44  ipcrm: permission denied for id (724467779)
% 0.21/0.44  ipcrm: permission denied for id (727515204)
% 0.21/0.45  ipcrm: permission denied for id (724533317)
% 0.21/0.45  ipcrm: permission denied for id (727547974)
% 0.21/0.45  ipcrm: permission denied for id (724598855)
% 0.21/0.45  ipcrm: permission denied for id (727580744)
% 0.21/0.45  ipcrm: permission denied for id (724664393)
% 0.21/0.45  ipcrm: permission denied for id (724697162)
% 0.21/0.45  ipcrm: permission denied for id (724729931)
% 0.21/0.45  ipcrm: permission denied for id (727613516)
% 0.21/0.46  ipcrm: permission denied for id (724795469)
% 0.21/0.46  ipcrm: permission denied for id (724828238)
% 0.21/0.46  ipcrm: permission denied for id (727646287)
% 0.21/0.46  ipcrm: permission denied for id (724893776)
% 0.21/0.46  ipcrm: permission denied for id (727679057)
% 0.21/0.46  ipcrm: permission denied for id (727711826)
% 0.21/0.46  ipcrm: permission denied for id (724992083)
% 0.21/0.46  ipcrm: permission denied for id (727744596)
% 0.21/0.47  ipcrm: permission denied for id (727777365)
% 0.21/0.47  ipcrm: permission denied for id (725090390)
% 0.21/0.47  ipcrm: permission denied for id (727842904)
% 0.21/0.47  ipcrm: permission denied for id (725188697)
% 0.21/0.47  ipcrm: permission denied for id (727875674)
% 0.21/0.48  ipcrm: permission denied for id (725319773)
% 0.21/0.48  ipcrm: permission denied for id (725385311)
% 0.21/0.48  ipcrm: permission denied for id (725450849)
% 0.21/0.48  ipcrm: permission denied for id (722141282)
% 0.21/0.48  ipcrm: permission denied for id (722174051)
% 0.21/0.48  ipcrm: permission denied for id (728039524)
% 0.21/0.49  ipcrm: permission denied for id (722206821)
% 0.21/0.49  ipcrm: permission denied for id (725516390)
% 0.21/0.49  ipcrm: permission denied for id (725549159)
% 0.21/0.49  ipcrm: permission denied for id (725581928)
% 0.21/0.49  ipcrm: permission denied for id (728105066)
% 0.21/0.49  ipcrm: permission denied for id (722272363)
% 0.21/0.50  ipcrm: permission denied for id (728203374)
% 0.21/0.50  ipcrm: permission denied for id (722337903)
% 0.21/0.50  ipcrm: permission denied for id (725811312)
% 0.21/0.50  ipcrm: permission denied for id (722370673)
% 0.21/0.50  ipcrm: permission denied for id (728268914)
% 0.21/0.50  ipcrm: permission denied for id (725876851)
% 0.21/0.50  ipcrm: permission denied for id (725909620)
% 0.21/0.51  ipcrm: permission denied for id (725942389)
% 0.21/0.51  ipcrm: permission denied for id (726007926)
% 0.21/0.51  ipcrm: permission denied for id (722436215)
% 0.21/0.51  ipcrm: permission denied for id (726073464)
% 0.21/0.51  ipcrm: permission denied for id (726106233)
% 0.21/0.51  ipcrm: permission denied for id (728301690)
% 0.21/0.51  ipcrm: permission denied for id (728367228)
% 0.21/0.52  ipcrm: permission denied for id (728399997)
% 0.21/0.52  ipcrm: permission denied for id (726270078)
% 0.21/0.52  ipcrm: permission denied for id (728432767)
% 0.80/0.60  % (9214)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.80/0.60  % (9213)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.80/0.61  % (9213)Refutation found. Thanks to Tanya!
% 0.80/0.61  % SZS status Theorem for theBenchmark
% 0.80/0.61  % SZS output start Proof for theBenchmark
% 0.80/0.61  fof(f101,plain,(
% 0.80/0.61    $false),
% 0.80/0.61    inference(resolution,[],[f92,f80])).
% 0.80/0.61  fof(f80,plain,(
% 0.80/0.61    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(trivial_inequality_removal,[],[f79])).
% 0.80/0.61  fof(f79,plain,(
% 0.80/0.61    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(backward_demodulation,[],[f46,f78])).
% 0.80/0.61  fof(f78,plain,(
% 0.80/0.61    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(duplicate_literal_removal,[],[f77])).
% 0.80/0.61  fof(f77,plain,(
% 0.80/0.61    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(resolution,[],[f76,f45])).
% 0.80/0.61  fof(f45,plain,(
% 0.80/0.61    ~r2_hidden(sK0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(definition_unfolding,[],[f27,f44])).
% 0.80/0.61  fof(f44,plain,(
% 0.80/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.80/0.61    inference(definition_unfolding,[],[f28,f43])).
% 0.80/0.61  fof(f43,plain,(
% 0.80/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.80/0.61    inference(definition_unfolding,[],[f30,f42])).
% 0.80/0.61  fof(f42,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.80/0.61    inference(definition_unfolding,[],[f37,f41])).
% 0.80/0.61  fof(f41,plain,(
% 0.80/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f7])).
% 0.80/0.61  fof(f7,axiom,(
% 0.80/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.80/0.61  fof(f37,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f6])).
% 0.80/0.61  fof(f6,axiom,(
% 0.80/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.80/0.61  fof(f30,plain,(
% 0.80/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f5])).
% 0.80/0.61  fof(f5,axiom,(
% 0.80/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.80/0.61  fof(f28,plain,(
% 0.80/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f4])).
% 0.80/0.61  fof(f4,axiom,(
% 0.80/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.80/0.61  fof(f27,plain,(
% 0.80/0.61    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(cnf_transformation,[],[f20])).
% 0.80/0.61  fof(f20,plain,(
% 0.80/0.61    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.80/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.80/0.61  fof(f19,plain,(
% 0.80/0.61    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.80/0.61    introduced(choice_axiom,[])).
% 0.80/0.61  fof(f18,plain,(
% 0.80/0.61    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.80/0.61    inference(flattening,[],[f17])).
% 0.80/0.61  % (9228)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.80/0.61  fof(f17,plain,(
% 0.80/0.61    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.80/0.61    inference(nnf_transformation,[],[f13])).
% 0.80/0.61  fof(f13,plain,(
% 0.80/0.61    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.80/0.61    inference(ennf_transformation,[],[f12])).
% 0.80/0.61  fof(f12,negated_conjecture,(
% 0.80/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.80/0.61    inference(negated_conjecture,[],[f11])).
% 0.80/0.61  fof(f11,conjecture,(
% 0.80/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.80/0.61  fof(f76,plain,(
% 0.80/0.61    ( ! [X4] : (r2_hidden(X4,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(X4,X4,X4,X4,X4))) )),
% 0.80/0.61    inference(resolution,[],[f73,f67])).
% 0.80/0.61  fof(f67,plain,(
% 0.80/0.61    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK1),X0) | k1_xboole_0 = k10_relat_1(sK1,X0)) )),
% 0.80/0.61    inference(resolution,[],[f32,f25])).
% 0.80/0.61  fof(f25,plain,(
% 0.80/0.61    v1_relat_1(sK1)),
% 0.80/0.61    inference(cnf_transformation,[],[f20])).
% 0.80/0.61  fof(f32,plain,(
% 0.80/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 0.80/0.61    inference(cnf_transformation,[],[f21])).
% 0.80/0.61  fof(f21,plain,(
% 0.80/0.61    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.80/0.61    inference(nnf_transformation,[],[f14])).
% 0.80/0.61  fof(f14,plain,(
% 0.80/0.61    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.80/0.61    inference(ennf_transformation,[],[f10])).
% 0.80/0.61  fof(f10,axiom,(
% 0.80/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.80/0.61  fof(f73,plain,(
% 0.80/0.61    ( ! [X2,X3] : (r1_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)) | r2_hidden(X2,X3)) )),
% 0.80/0.61    inference(resolution,[],[f47,f34])).
% 0.80/0.61  fof(f34,plain,(
% 0.80/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f16])).
% 0.80/0.61  fof(f16,plain,(
% 0.80/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.80/0.61    inference(ennf_transformation,[],[f1])).
% 0.80/0.61  fof(f1,axiom,(
% 0.80/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.80/0.61  fof(f47,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.80/0.61    inference(definition_unfolding,[],[f33,f44])).
% 0.80/0.61  fof(f33,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f15])).
% 0.80/0.61  fof(f15,plain,(
% 0.80/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.80/0.61    inference(ennf_transformation,[],[f8])).
% 0.80/0.61  fof(f8,axiom,(
% 0.80/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.80/0.61  fof(f46,plain,(
% 0.80/0.61    k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(definition_unfolding,[],[f26,f44])).
% 0.80/0.61  fof(f26,plain,(
% 0.80/0.61    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(cnf_transformation,[],[f20])).
% 0.80/0.61  fof(f92,plain,(
% 0.80/0.61    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.80/0.61    inference(superposition,[],[f84,f87])).
% 0.80/0.61  fof(f87,plain,(
% 0.80/0.61    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(resolution,[],[f85,f35])).
% 0.80/0.61  fof(f35,plain,(
% 0.80/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.80/0.61    inference(cnf_transformation,[],[f22])).
% 0.80/0.61  fof(f22,plain,(
% 0.80/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.80/0.61    inference(nnf_transformation,[],[f3])).
% 0.80/0.61  fof(f3,axiom,(
% 0.80/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.80/0.61  fof(f85,plain,(
% 0.80/0.61    r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(resolution,[],[f82,f25])).
% 0.80/0.61  fof(f82,plain,(
% 0.80/0.61    ~v1_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.80/0.61    inference(trivial_inequality_removal,[],[f81])).
% 0.80/0.61  fof(f81,plain,(
% 0.80/0.61    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1)),
% 0.80/0.61    inference(superposition,[],[f31,f78])).
% 0.80/0.61  fof(f31,plain,(
% 0.80/0.61    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f21])).
% 0.80/0.61  fof(f84,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.80/0.61    inference(trivial_inequality_removal,[],[f83])).
% 0.80/0.61  fof(f83,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) | ~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.80/0.61    inference(superposition,[],[f49,f54])).
% 0.80/0.61  fof(f54,plain,(
% 0.80/0.61    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 0.80/0.61    inference(resolution,[],[f35,f51])).
% 0.80/0.61  fof(f51,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.80/0.61    inference(resolution,[],[f34,f29])).
% 0.80/0.61  fof(f29,plain,(
% 0.80/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f2])).
% 0.80/0.61  fof(f2,axiom,(
% 0.80/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.80/0.61  fof(f49,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 0.80/0.61    inference(definition_unfolding,[],[f39,f43,f43])).
% 0.80/0.61  fof(f39,plain,(
% 0.80/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.80/0.61    inference(cnf_transformation,[],[f24])).
% 0.80/0.61  fof(f24,plain,(
% 0.80/0.61    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.80/0.61    inference(flattening,[],[f23])).
% 0.80/0.61  fof(f23,plain,(
% 0.80/0.61    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.80/0.61    inference(nnf_transformation,[],[f9])).
% 0.80/0.61  fof(f9,axiom,(
% 0.80/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.80/0.61  % SZS output end Proof for theBenchmark
% 0.80/0.61  % (9213)------------------------------
% 0.80/0.61  % (9213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.61  % (9213)Termination reason: Refutation
% 0.80/0.61  
% 0.80/0.61  % (9213)Memory used [KB]: 1663
% 0.80/0.61  % (9213)Time elapsed: 0.028 s
% 0.80/0.61  % (9213)------------------------------
% 0.80/0.61  % (9213)------------------------------
% 0.80/0.61  % (9073)Success in time 0.255 s
%------------------------------------------------------------------------------
