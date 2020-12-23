%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:44 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  99 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  181 ( 291 expanded)
%              Number of equality atoms :   33 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(subsumption_resolution,[],[f452,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f452,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f451,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f451,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f450,f265])).

fof(f265,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f264,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f264,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f263,f34])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f263,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f255,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f255,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f71,f135])).

fof(f135,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f134,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f134,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f53,f39])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f71,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f67,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f35,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f450,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f430,f33])).

fof(f430,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f35,f310])).

fof(f310,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,k1_tarski(X4))
      | ~ v1_relat_1(X3)
      | r2_hidden(X4,k1_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_xboole_0 = k7_relat_1(X3,k1_tarski(X4))
      | r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f199,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f199,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k7_relat_1(X0,k1_tarski(X1))))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f90,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X4)))
      | k1_xboole_0 = k7_relat_1(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f82,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,X4)
      | ~ r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (16483)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.54  % (16492)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.56  % (16502)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.56  % (16485)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.57  % (16493)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.57  % (16504)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.57  % (16482)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.57  % (16494)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (16497)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.58  % (16487)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  % (16481)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.59  % (16500)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.59  % (16481)Refutation not found, incomplete strategy% (16481)------------------------------
% 1.56/0.59  % (16481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (16481)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (16481)Memory used [KB]: 1663
% 1.56/0.59  % (16481)Time elapsed: 0.161 s
% 1.56/0.59  % (16481)------------------------------
% 1.56/0.59  % (16481)------------------------------
% 1.56/0.59  % (16480)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.59  % (16486)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.59  % (16507)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.60  % (16506)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.60  % (16499)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.60  % (16511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.60  % (16501)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.60  % (16490)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.60  % (16511)Refutation not found, incomplete strategy% (16511)------------------------------
% 1.56/0.60  % (16511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (16511)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.60  
% 1.56/0.60  % (16511)Memory used [KB]: 10746
% 1.56/0.60  % (16511)Time elapsed: 0.174 s
% 1.56/0.60  % (16511)------------------------------
% 1.56/0.60  % (16511)------------------------------
% 1.56/0.60  % (16489)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.60  % (16509)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.61  % (16506)Refutation not found, incomplete strategy% (16506)------------------------------
% 1.56/0.61  % (16506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (16509)Refutation not found, incomplete strategy% (16509)------------------------------
% 1.56/0.61  % (16509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (16509)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16509)Memory used [KB]: 6140
% 1.56/0.61  % (16509)Time elapsed: 0.184 s
% 1.56/0.61  % (16509)------------------------------
% 1.56/0.61  % (16509)------------------------------
% 1.56/0.61  % (16512)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.61  % (16512)Refutation not found, incomplete strategy% (16512)------------------------------
% 1.56/0.61  % (16512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (16512)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16512)Memory used [KB]: 1663
% 1.56/0.61  % (16512)Time elapsed: 0.183 s
% 1.56/0.61  % (16512)------------------------------
% 1.56/0.61  % (16512)------------------------------
% 1.56/0.61  % (16491)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.56/0.61  % (16491)Refutation not found, incomplete strategy% (16491)------------------------------
% 1.56/0.61  % (16491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (16491)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16491)Memory used [KB]: 10746
% 1.56/0.61  % (16491)Time elapsed: 0.183 s
% 1.56/0.61  % (16491)------------------------------
% 1.56/0.61  % (16491)------------------------------
% 1.56/0.61  % (16506)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16506)Memory used [KB]: 10618
% 1.56/0.61  % (16506)Time elapsed: 0.182 s
% 1.56/0.61  % (16506)------------------------------
% 1.56/0.61  % (16506)------------------------------
% 1.56/0.61  % (16495)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.61  % (16495)Refutation not found, incomplete strategy% (16495)------------------------------
% 1.56/0.61  % (16495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (16495)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (16495)Memory used [KB]: 1663
% 1.56/0.61  % (16495)Time elapsed: 0.183 s
% 1.56/0.61  % (16495)------------------------------
% 1.56/0.61  % (16495)------------------------------
% 1.56/0.61  % (16503)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.56/0.62  % (16498)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.62  % (16508)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.62  % (16498)Refutation not found, incomplete strategy% (16498)------------------------------
% 1.56/0.62  % (16498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (16498)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (16498)Memory used [KB]: 10618
% 1.56/0.62  % (16498)Time elapsed: 0.193 s
% 1.56/0.62  % (16498)------------------------------
% 1.56/0.62  % (16498)------------------------------
% 1.56/0.63  % (16488)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.63  % (16505)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.63  % (16490)Refutation found. Thanks to Tanya!
% 1.56/0.63  % SZS status Theorem for theBenchmark
% 1.56/0.65  % SZS output start Proof for theBenchmark
% 1.56/0.65  fof(f453,plain,(
% 1.56/0.65    $false),
% 1.56/0.65    inference(subsumption_resolution,[],[f452,f38])).
% 1.56/0.65  fof(f38,plain,(
% 1.56/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.65    inference(cnf_transformation,[],[f2])).
% 1.56/0.65  fof(f2,axiom,(
% 1.56/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.65  fof(f452,plain,(
% 1.56/0.65    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.56/0.65    inference(forward_demodulation,[],[f451,f37])).
% 1.56/0.65  fof(f37,plain,(
% 1.56/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.56/0.65    inference(cnf_transformation,[],[f10])).
% 1.56/0.65  fof(f10,axiom,(
% 1.56/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.56/0.65  fof(f451,plain,(
% 1.56/0.65    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.56/0.65    inference(subsumption_resolution,[],[f450,f265])).
% 1.56/0.65  fof(f265,plain,(
% 1.56/0.65    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.56/0.65    inference(subsumption_resolution,[],[f264,f33])).
% 1.56/0.65  fof(f33,plain,(
% 1.56/0.65    v1_relat_1(sK1)),
% 1.56/0.65    inference(cnf_transformation,[],[f28])).
% 1.56/0.65  fof(f28,plain,(
% 1.56/0.65    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.56/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).
% 1.56/0.65  fof(f27,plain,(
% 1.56/0.65    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.56/0.65    introduced(choice_axiom,[])).
% 1.56/0.65  fof(f17,plain,(
% 1.56/0.65    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.56/0.65    inference(flattening,[],[f16])).
% 1.56/0.65  fof(f16,plain,(
% 1.56/0.65    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.56/0.65    inference(ennf_transformation,[],[f15])).
% 1.56/0.65  fof(f15,negated_conjecture,(
% 1.56/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.56/0.65    inference(negated_conjecture,[],[f14])).
% 1.56/0.65  fof(f14,conjecture,(
% 1.56/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.56/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).
% 1.56/0.65  fof(f264,plain,(
% 1.56/0.65    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.56/0.65    inference(subsumption_resolution,[],[f263,f34])).
% 1.56/0.65  fof(f34,plain,(
% 1.56/0.65    v1_funct_1(sK1)),
% 1.56/0.65    inference(cnf_transformation,[],[f28])).
% 1.56/0.65  fof(f263,plain,(
% 1.56/0.65    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.56/0.65    inference(subsumption_resolution,[],[f255,f54])).
% 1.56/0.65  fof(f54,plain,(
% 1.56/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.65    inference(equality_resolution,[],[f46])).
% 1.56/0.65  fof(f46,plain,(
% 1.56/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.65    inference(cnf_transformation,[],[f30])).
% 2.20/0.65  fof(f30,plain,(
% 2.20/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.65    inference(flattening,[],[f29])).
% 2.20/0.65  fof(f29,plain,(
% 2.20/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.65    inference(nnf_transformation,[],[f1])).
% 2.20/0.65  fof(f1,axiom,(
% 2.20/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.20/0.65  fof(f255,plain,(
% 2.20/0.65    ~r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 2.20/0.65    inference(superposition,[],[f71,f135])).
% 2.20/0.65  fof(f135,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f134,f39])).
% 2.20/0.65  fof(f39,plain,(
% 2.20/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f3])).
% 2.20/0.65  fof(f3,axiom,(
% 2.20/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.20/0.65  fof(f134,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.20/0.65    inference(duplicate_literal_removal,[],[f131])).
% 2.20/0.65  fof(f131,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.20/0.65    inference(superposition,[],[f53,f39])).
% 2.20/0.65  fof(f53,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f26])).
% 2.20/0.65  fof(f26,plain,(
% 2.20/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.20/0.65    inference(flattening,[],[f25])).
% 2.20/0.65  fof(f25,plain,(
% 2.20/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.20/0.65    inference(ennf_transformation,[],[f13])).
% 2.20/0.65  fof(f13,axiom,(
% 2.20/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 2.20/0.65  fof(f71,plain,(
% 2.20/0.65    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))),
% 2.20/0.65    inference(subsumption_resolution,[],[f67,f33])).
% 2.20/0.65  fof(f67,plain,(
% 2.20/0.65    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 2.20/0.65    inference(superposition,[],[f35,f43])).
% 2.20/0.65  fof(f43,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f20])).
% 2.20/0.65  fof(f20,plain,(
% 2.20/0.65    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.65    inference(ennf_transformation,[],[f8])).
% 2.20/0.65  fof(f8,axiom,(
% 2.20/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.20/0.65  fof(f35,plain,(
% 2.20/0.65    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 2.20/0.65    inference(cnf_transformation,[],[f28])).
% 2.20/0.65  fof(f450,plain,(
% 2.20/0.65    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | r2_hidden(sK0,k1_relat_1(sK1))),
% 2.20/0.65    inference(subsumption_resolution,[],[f430,f33])).
% 2.20/0.65  fof(f430,plain,(
% 2.20/0.65    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(sK1))),
% 2.20/0.65    inference(superposition,[],[f35,f310])).
% 2.20/0.65  fof(f310,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k1_xboole_0 = k7_relat_1(X3,k1_tarski(X4)) | ~v1_relat_1(X3) | r2_hidden(X4,k1_relat_1(X3))) )),
% 2.20/0.65    inference(duplicate_literal_removal,[],[f302])).
% 2.20/0.65  fof(f302,plain,(
% 2.20/0.65    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_xboole_0 = k7_relat_1(X3,k1_tarski(X4)) | r2_hidden(X4,k1_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 2.20/0.65    inference(resolution,[],[f199,f51])).
% 2.20/0.65  fof(f51,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f32])).
% 2.20/0.65  fof(f32,plain,(
% 2.20/0.65    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.20/0.65    inference(flattening,[],[f31])).
% 2.20/0.65  fof(f31,plain,(
% 2.20/0.65    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.20/0.65    inference(nnf_transformation,[],[f24])).
% 2.20/0.65  fof(f24,plain,(
% 2.20/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 2.20/0.65    inference(ennf_transformation,[],[f11])).
% 2.20/0.65  fof(f11,axiom,(
% 2.20/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 2.20/0.65  fof(f199,plain,(
% 2.20/0.65    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(k7_relat_1(X0,k1_tarski(X1)))) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_tarski(X1))) )),
% 2.20/0.65    inference(resolution,[],[f90,f44])).
% 2.20/0.65  fof(f44,plain,(
% 2.20/0.65    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f21])).
% 2.20/0.65  fof(f21,plain,(
% 2.20/0.65    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.20/0.65    inference(ennf_transformation,[],[f6])).
% 2.20/0.65  fof(f6,axiom,(
% 2.20/0.65    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.20/0.65  fof(f90,plain,(
% 2.20/0.65    ( ! [X4,X3] : (~r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X4))) | k1_xboole_0 = k7_relat_1(X3,X4) | ~v1_relat_1(X3)) )),
% 2.20/0.65    inference(subsumption_resolution,[],[f82,f42])).
% 2.20/0.65  fof(f42,plain,(
% 2.20/0.65    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f19])).
% 2.20/0.66  fof(f19,plain,(
% 2.20/0.66    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.20/0.66    inference(ennf_transformation,[],[f7])).
% 2.20/0.66  fof(f7,axiom,(
% 2.20/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.20/0.66  fof(f82,plain,(
% 2.20/0.66    ( ! [X4,X3] : (k1_xboole_0 = k7_relat_1(X3,X4) | ~r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 2.20/0.66    inference(superposition,[],[f49,f40])).
% 2.20/0.66  fof(f40,plain,(
% 2.20/0.66    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f18])).
% 2.20/0.66  fof(f18,plain,(
% 2.20/0.66    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.20/0.66    inference(ennf_transformation,[],[f12])).
% 2.20/0.66  fof(f12,axiom,(
% 2.20/0.66    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 2.20/0.66  fof(f49,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f23])).
% 2.20/0.66  fof(f23,plain,(
% 2.20/0.66    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 2.20/0.66    inference(flattening,[],[f22])).
% 2.20/0.66  fof(f22,plain,(
% 2.20/0.66    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.20/0.66    inference(ennf_transformation,[],[f9])).
% 2.20/0.66  fof(f9,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 2.20/0.66  % SZS output end Proof for theBenchmark
% 2.20/0.66  % (16490)------------------------------
% 2.20/0.66  % (16490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (16490)Termination reason: Refutation
% 2.20/0.66  
% 2.20/0.66  % (16490)Memory used [KB]: 1918
% 2.20/0.66  % (16490)Time elapsed: 0.214 s
% 2.20/0.66  % (16490)------------------------------
% 2.20/0.66  % (16490)------------------------------
% 2.20/0.66  % (16475)Success in time 0.293 s
%------------------------------------------------------------------------------
