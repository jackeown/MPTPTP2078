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
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 672 expanded)
%              Number of leaves         :   19 ( 196 expanded)
%              Depth                    :   21
%              Number of atoms          :  372 (2993 expanded)
%              Number of equality atoms :  185 (1455 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(equality_resolution,[],[f445])).

fof(f445,plain,(
    ! [X13] : sK1 != X13 ),
    inference(subsumption_resolution,[],[f443,f173])).

fof(f173,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f44,f172])).

fof(f172,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f171,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f170,f112])).

fof(f112,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f110,f94])).

fof(f94,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f57,f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f47,f57])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

% (24337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f57,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(condensation,[],[f109])).

fof(f109,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
      | k1_xboole_0 != X3 ) ),
    inference(resolution,[],[f49,f93])).

fof(f93,plain,(
    ! [X2] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f55,f90])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

% (24324)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f170,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(condensation,[],[f169])).

fof(f169,plain,(
    ! [X3] :
      ( k1_xboole_0 != sK1
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
      | k1_xboole_0 != X3 ) ),
    inference(forward_demodulation,[],[f168,f94])).

fof(f168,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
      | k1_xboole_0 != X3 ) ),
    inference(subsumption_resolution,[],[f164,f93])).

fof(f164,plain,(
    ! [X3] :
      ( sK1 != k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X3 ) ),
    inference(resolution,[],[f45,f92])).

fof(f92,plain,(
    ! [X1] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f56,f90])).

fof(f56,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f443,plain,(
    ! [X13] :
      ( k1_xboole_0 = sK0
      | sK1 != X13 ) ),
    inference(resolution,[],[f429,f311])).

% (24325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f311,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 != X1 ) ),
    inference(resolution,[],[f309,f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f302,f178])).

fof(f178,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f177,f46])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f175,f112])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
      | sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f166,f90])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | sK1 != X0 ) ),
    inference(forward_demodulation,[],[f165,f57])).

fof(f165,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK3(X0))
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK3(X0))
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f45,f56])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f299,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f298,f178])).

fof(f298,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f167,f53])).

% (24352)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f167,plain,(
    ! [X2,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X2))
      | ~ r1_tarski(k2_relat_1(sK2(X1,X2)),sK0)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,(
    ! [X2,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X2))
      | ~ r1_tarski(k2_relat_1(sK2(X1,X2)),sK0)
      | ~ v1_relat_1(sK2(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f309,plain,(
    ! [X1] :
      ( r1_tarski(k1_tarski(X1),sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f62,f307])).

fof(f307,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(resolution,[],[f303,f86])).

fof(f86,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_tarski(X1),X2)
      | sK4(k1_tarski(X1),X2) = X1 ) ),
    inference(resolution,[],[f61,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

% (24350)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f429,plain,(
    ! [X8] :
      ( r2_hidden(sK6(k1_xboole_0,X8),X8)
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f417,f94])).

fof(f417,plain,(
    ! [X8] :
      ( k1_relat_1(k1_xboole_0) = X8
      | r2_hidden(sK6(k1_xboole_0,X8),X8) ) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f59,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

% (24325)Refutation not found, incomplete strategy% (24325)------------------------------
% (24325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24325)Termination reason: Refutation not found, incomplete strategy

% (24325)Memory used [KB]: 10746
% (24325)Time elapsed: 0.127 s
% (24325)------------------------------
% (24325)------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (24323)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (24330)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (24323)Refutation not found, incomplete strategy% (24323)------------------------------
% 0.22/0.51  % (24323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24323)Memory used [KB]: 1663
% 0.22/0.51  % (24323)Time elapsed: 0.094 s
% 0.22/0.51  % (24323)------------------------------
% 0.22/0.51  % (24323)------------------------------
% 0.22/0.51  % (24328)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (24338)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (24345)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (24326)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (24343)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (24335)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24329)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (24332)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (24332)Refutation not found, incomplete strategy% (24332)------------------------------
% 0.22/0.53  % (24332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24332)Memory used [KB]: 10618
% 0.22/0.53  % (24332)Time elapsed: 0.114 s
% 0.22/0.53  % (24332)------------------------------
% 0.22/0.53  % (24332)------------------------------
% 0.22/0.53  % (24331)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (24331)Refutation not found, incomplete strategy% (24331)------------------------------
% 0.22/0.53  % (24331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24331)Memory used [KB]: 10746
% 0.22/0.53  % (24331)Time elapsed: 0.117 s
% 0.22/0.53  % (24331)------------------------------
% 0.22/0.53  % (24331)------------------------------
% 0.22/0.54  % (24351)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (24336)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (24330)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (24349)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(equality_resolution,[],[f445])).
% 0.22/0.54  fof(f445,plain,(
% 0.22/0.54    ( ! [X13] : (sK1 != X13) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f443,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f44,f172])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(subsumption_resolution,[],[f171,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != sK1),
% 0.22/0.54    inference(forward_demodulation,[],[f170,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(equality_resolution,[],[f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != X0 | k1_relat_1(k1_xboole_0) = X0) )),
% 0.22/0.54    inference(superposition,[],[f57,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = sK3(X0) | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f89,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK3(X0) | ~v1_relat_1(sK3(X0))) )),
% 0.22/0.54    inference(superposition,[],[f47,f57])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  % (24337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(condensation,[],[f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0) | k1_xboole_0 != X3) )),
% 0.22/0.54    inference(resolution,[],[f49,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X2] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X2) )),
% 0.22/0.54    inference(superposition,[],[f55,f90])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f17])).
% 0.22/0.54  % (24324)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 0.22/0.54    inference(condensation,[],[f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 != sK1 | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | k1_xboole_0 != X3) )),
% 0.22/0.54    inference(forward_demodulation,[],[f168,f94])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ( ! [X3] : (sK1 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | k1_xboole_0 != X3) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f164,f93])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X3] : (sK1 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != X3) )),
% 0.22/0.54    inference(resolution,[],[f45,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X1] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(superposition,[],[f56,f90])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f443,plain,(
% 0.22/0.54    ( ! [X13] : (k1_xboole_0 = sK0 | sK1 != X13) )),
% 0.22/0.54    inference(resolution,[],[f429,f311])).
% 0.22/0.54  % (24325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK1 != X1) )),
% 0.22/0.54    inference(resolution,[],[f309,f303])).
% 0.22/0.54  fof(f303,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f302,f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f46])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != X0 | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f175,f112])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | sK1 != X0 | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(superposition,[],[f166,f90])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3(X0)),sK0) | sK1 != X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f165,f57])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK3(X0)) | ~r1_tarski(k2_relat_1(sK3(X0)),sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f162,f55])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK3(X0)) | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_relat_1(sK3(X0))) )),
% 0.22/0.54    inference(resolution,[],[f45,f56])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != X0 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(superposition,[],[f299,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | sK1 != X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f298,f178])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f297])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(superposition,[],[f167,f53])).
% 0.22/0.54  % (24352)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X2,X1] : (sK1 != k1_relat_1(sK2(X1,X2)) | ~r1_tarski(k2_relat_1(sK2(X1,X2)),sK0) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f163,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X2,X1] : (sK1 != k1_relat_1(sK2(X1,X2)) | ~r1_tarski(k2_relat_1(sK2(X1,X2)),sK0) | ~v1_relat_1(sK2(X1,X2)) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(resolution,[],[f45,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(k1_tarski(X1),sK0) | ~r2_hidden(X1,sK0)) )),
% 0.22/0.54    inference(superposition,[],[f62,f307])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 0.22/0.54    inference(equality_resolution,[],[f304])).
% 0.22/0.54  fof(f304,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 0.22/0.54    inference(resolution,[],[f303,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),X2) | sK4(k1_tarski(X1),X2) = X1) )),
% 0.22/0.54    inference(resolution,[],[f61,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.22/0.54  % (24350)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f429,plain,(
% 0.22/0.54    ( ! [X8] : (r2_hidden(sK6(k1_xboole_0,X8),X8) | k1_xboole_0 = X8) )),
% 0.22/0.54    inference(forward_demodulation,[],[f417,f94])).
% 0.22/0.54  fof(f417,plain,(
% 0.22/0.54    ( ! [X8] : (k1_relat_1(k1_xboole_0) = X8 | r2_hidden(sK6(k1_xboole_0,X8),X8)) )),
% 0.22/0.54    inference(resolution,[],[f69,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f59,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  % (24325)Refutation not found, incomplete strategy% (24325)------------------------------
% 0.22/0.54  % (24325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24325)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24325)Memory used [KB]: 10746
% 0.22/0.54  % (24325)Time elapsed: 0.127 s
% 0.22/0.54  % (24325)------------------------------
% 0.22/0.54  % (24325)------------------------------
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f37,f40,f39,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24330)------------------------------
% 0.22/0.54  % (24330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24330)Termination reason: Refutation
% 0.22/0.54  % (24345)Refutation not found, incomplete strategy% (24345)------------------------------
% 0.22/0.54  % (24345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24345)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24345)Memory used [KB]: 10746
% 0.22/0.54  % (24345)Time elapsed: 0.079 s
% 0.22/0.54  % (24345)------------------------------
% 0.22/0.54  % (24345)------------------------------
% 0.22/0.54  
% 0.22/0.54  % (24330)Memory used [KB]: 6780
% 0.22/0.54  % (24330)Time elapsed: 0.121 s
% 0.22/0.54  % (24330)------------------------------
% 0.22/0.54  % (24330)------------------------------
% 0.22/0.54  % (24347)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (24320)Success in time 0.181 s
%------------------------------------------------------------------------------
