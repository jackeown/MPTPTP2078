%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 241 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :   24
%              Number of atoms          :  223 ( 852 expanded)
%              Number of equality atoms :  105 ( 406 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f147,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f55,f131])).

fof(f131,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f97,f120])).

fof(f120,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f43,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

% (11953)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f119,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f51,f113])).

fof(f113,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f110,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X2 ) ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X2
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X2
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f57,f86])).

fof(f86,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f78,f66])).

fof(f66,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f78,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f67,f76])).

fof(f76,plain,(
    sK1 = k7_relat_1(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),X0)
      | sK1 = k7_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f52,f42])).

fof(f42,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f67,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

% (11953)Refutation not found, incomplete strategy% (11953)------------------------------
% (11953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11953)Termination reason: Refutation not found, incomplete strategy

% (11953)Memory used [KB]: 1791
% (11953)Time elapsed: 0.104 s
% (11953)------------------------------
% (11953)------------------------------
% (11972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f96,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f95,f76])).

fof(f95,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f94,f42])).

fof(f94,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f93,f76])).

fof(f93,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f75,f78])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f49,f67])).

% (11971)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (11964)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (11979)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (11966)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (11954)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (11967)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (11975)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (11963)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (11958)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11965)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (11952)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (11966)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f147,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f55,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.52    inference(superposition,[],[f97,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  % (11953)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.52    inference(equality_resolution,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1) | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f51,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f110,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2 | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f91,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f40])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X0),sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f57,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.21/0.52    inference(superposition,[],[f78,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.21/0.52    inference(resolution,[],[f40,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.52    inference(superposition,[],[f67,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    sK1 = k7_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.52    inference(resolution,[],[f71,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0) | sK1 = k7_relat_1(sK1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f40])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0) | sK1 = k7_relat_1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f52,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) )),
% 0.21/0.52    inference(resolution,[],[f40,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  % (11953)Refutation not found, incomplete strategy% (11953)------------------------------
% 0.21/0.52  % (11953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11953)Memory used [KB]: 1791
% 0.21/0.52  % (11953)Time elapsed: 0.104 s
% 0.21/0.52  % (11953)------------------------------
% 0.21/0.52  % (11953)------------------------------
% 0.21/0.52  % (11972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f40])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 != k2_relat_1(sK1)),
% 0.21/0.52    inference(forward_demodulation,[],[f95,f76])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f94,f42])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK1) | k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f93,f76])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) | ~v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))),
% 0.21/0.52    inference(superposition,[],[f75,f78])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.21/0.52    inference(superposition,[],[f49,f67])).
% 0.21/0.52  % (11971)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11966)------------------------------
% 0.21/0.52  % (11966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11966)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11966)Memory used [KB]: 1791
% 0.21/0.52  % (11966)Time elapsed: 0.061 s
% 0.21/0.52  % (11966)------------------------------
% 0.21/0.52  % (11966)------------------------------
% 0.21/0.52  % (11951)Success in time 0.166 s
%------------------------------------------------------------------------------
