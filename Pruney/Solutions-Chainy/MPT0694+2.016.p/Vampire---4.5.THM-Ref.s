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
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   54 (  96 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   21
%              Number of atoms          :  149 ( 280 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f170,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f170,plain,(
    ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f169,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f169,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f168,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f146,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f146,plain,(
    ! [X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k10_relat_1(sK2,sK1)),sK1)
      | ~ r1_tarski(sK2,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f124,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f60,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f124,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),X5)
      | ~ r1_tarski(k9_relat_1(X4,X5),sK1)
      | ~ r1_tarski(sK2,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f123,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k9_relat_1(X4,X5),sK1)
      | ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),X5)
      | ~ r1_tarski(sK2,X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f111,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(subsumption_resolution,[],[f110,f36])).

fof(f110,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(subsumption_resolution,[],[f109,f56])).

fof(f109,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(subsumption_resolution,[],[f108,f60])).

fof(f108,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f55,f58])).

fof(f58,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f38,f40])).

fof(f38,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:33:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (20652)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (20644)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (20637)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (20638)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.21/0.53  % (20628)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.53  % (20626)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.53  % (20625)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.54  % (20630)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.54  % (20629)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.21/0.54  % (20627)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.54  % (20646)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.21/0.54  % (20648)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.21/0.54  % (20642)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.21/0.54  % (20640)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (20645)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.55  % (20654)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.55  % (20636)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.55  % (20632)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (20641)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (20635)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.55  % (20634)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.56  % (20643)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.56  % (20653)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.57  % (20633)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.57  % (20647)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.57  % (20651)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.57  % (20631)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.57  % (20650)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.57  % (20641)Refutation not found, incomplete strategy% (20641)------------------------------
% 1.38/0.57  % (20641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (20641)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (20641)Memory used [KB]: 10618
% 1.38/0.57  % (20641)Time elapsed: 0.157 s
% 1.38/0.57  % (20641)------------------------------
% 1.38/0.57  % (20641)------------------------------
% 1.38/0.58  % (20649)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.58  % (20634)Refutation found. Thanks to Tanya!
% 1.38/0.58  % SZS status Theorem for theBenchmark
% 1.38/0.58  % SZS output start Proof for theBenchmark
% 1.38/0.58  fof(f171,plain,(
% 1.38/0.58    $false),
% 1.38/0.58    inference(subsumption_resolution,[],[f170,f37])).
% 1.38/0.58  fof(f37,plain,(
% 1.38/0.58    v1_funct_1(sK2)),
% 1.38/0.58    inference(cnf_transformation,[],[f33])).
% 1.38/0.58  fof(f33,plain,(
% 1.38/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).
% 1.38/0.58  fof(f32,plain,(
% 1.38/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f19,plain,(
% 1.38/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.38/0.58    inference(flattening,[],[f18])).
% 1.38/0.58  fof(f18,plain,(
% 1.38/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.38/0.58    inference(ennf_transformation,[],[f17])).
% 1.38/0.58  fof(f17,negated_conjecture,(
% 1.38/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.38/0.58    inference(negated_conjecture,[],[f16])).
% 1.38/0.58  fof(f16,conjecture,(
% 1.38/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 1.38/0.58  fof(f170,plain,(
% 1.38/0.58    ~v1_funct_1(sK2)),
% 1.38/0.58    inference(subsumption_resolution,[],[f169,f36])).
% 1.38/0.58  fof(f36,plain,(
% 1.38/0.58    v1_relat_1(sK2)),
% 1.38/0.58    inference(cnf_transformation,[],[f33])).
% 1.38/0.58  fof(f169,plain,(
% 1.38/0.58    ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 1.38/0.58    inference(subsumption_resolution,[],[f168,f56])).
% 1.38/0.58  fof(f56,plain,(
% 1.38/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.58    inference(equality_resolution,[],[f48])).
% 1.38/0.58  fof(f48,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.58    inference(cnf_transformation,[],[f35])).
% 1.38/0.58  fof(f35,plain,(
% 1.38/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.58    inference(flattening,[],[f34])).
% 1.38/0.58  fof(f34,plain,(
% 1.38/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.58    inference(nnf_transformation,[],[f2])).
% 1.38/0.58  fof(f2,axiom,(
% 1.38/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.58  fof(f168,plain,(
% 1.38/0.58    ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f166])).
% 1.38/0.58  fof(f166,plain,(
% 1.38/0.58    ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.38/0.58    inference(resolution,[],[f146,f46])).
% 1.38/0.58  fof(f46,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f23])).
% 1.38/0.58  fof(f23,plain,(
% 1.38/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.58    inference(flattening,[],[f22])).
% 1.38/0.58  fof(f22,plain,(
% 1.38/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.38/0.58    inference(ennf_transformation,[],[f15])).
% 1.38/0.58  fof(f15,axiom,(
% 1.38/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.38/0.58  fof(f146,plain,(
% 1.38/0.58    ( ! [X2] : (~r1_tarski(k9_relat_1(X2,k10_relat_1(sK2,sK1)),sK1) | ~r1_tarski(sK2,X2) | ~v1_relat_1(X2)) )),
% 1.38/0.58    inference(resolution,[],[f124,f61])).
% 1.38/0.58  fof(f61,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.38/0.58    inference(superposition,[],[f60,f40])).
% 1.38/0.58  fof(f40,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f1])).
% 1.38/0.58  fof(f1,axiom,(
% 1.38/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.38/0.58  fof(f60,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.38/0.58    inference(superposition,[],[f39,f43])).
% 1.38/0.58  fof(f43,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f6])).
% 1.38/0.58  fof(f6,axiom,(
% 1.38/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.58  fof(f39,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f5])).
% 1.38/0.58  fof(f5,axiom,(
% 1.38/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.38/0.58  fof(f124,plain,(
% 1.38/0.58    ( ! [X4,X5] : (~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),X5) | ~r1_tarski(k9_relat_1(X4,X5),sK1) | ~r1_tarski(sK2,X4) | ~v1_relat_1(X4)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f123,f36])).
% 1.38/0.58  fof(f123,plain,(
% 1.38/0.58    ( ! [X4,X5] : (~r1_tarski(k9_relat_1(X4,X5),sK1) | ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),X5) | ~r1_tarski(sK2,X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK2)) )),
% 1.38/0.58    inference(resolution,[],[f117,f53])).
% 1.38/0.58  fof(f53,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f27])).
% 1.38/0.58  fof(f27,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.38/0.58    inference(flattening,[],[f26])).
% 1.38/0.58  fof(f26,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.38/0.58    inference(ennf_transformation,[],[f13])).
% 1.38/0.58  fof(f13,axiom,(
% 1.38/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.38/0.58  fof(f117,plain,(
% 1.38/0.58    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0) | ~r1_tarski(X0,sK1)) )),
% 1.38/0.58    inference(resolution,[],[f111,f54])).
% 1.38/0.58  fof(f54,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f29])).
% 1.38/0.58  fof(f29,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.58    inference(flattening,[],[f28])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.58    inference(ennf_transformation,[],[f4])).
% 1.38/0.58  fof(f4,axiom,(
% 1.38/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.38/0.58  fof(f111,plain,(
% 1.38/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(subsumption_resolution,[],[f110,f36])).
% 1.38/0.58  fof(f110,plain,(
% 1.38/0.58    ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(subsumption_resolution,[],[f109,f56])).
% 1.38/0.58  fof(f109,plain,(
% 1.38/0.58    ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(subsumption_resolution,[],[f108,f60])).
% 1.38/0.58  fof(f108,plain,(
% 1.38/0.58    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f101])).
% 1.38/0.58  fof(f101,plain,(
% 1.38/0.58    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(resolution,[],[f53,f83])).
% 1.38/0.58  fof(f83,plain,(
% 1.38/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.38/0.58    inference(resolution,[],[f55,f58])).
% 1.38/0.58  fof(f58,plain,(
% 1.38/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 1.38/0.58    inference(backward_demodulation,[],[f38,f40])).
% 1.38/0.58  fof(f38,plain,(
% 1.38/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 1.38/0.58    inference(cnf_transformation,[],[f33])).
% 1.38/0.58  fof(f55,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f31])).
% 1.38/0.58  fof(f31,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.58    inference(flattening,[],[f30])).
% 1.38/0.58  fof(f30,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.58    inference(ennf_transformation,[],[f3])).
% 1.38/0.58  fof(f3,axiom,(
% 1.38/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.38/0.58  % SZS output end Proof for theBenchmark
% 1.38/0.58  % (20634)------------------------------
% 1.38/0.58  % (20634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (20634)Termination reason: Refutation
% 1.38/0.58  
% 1.38/0.58  % (20634)Memory used [KB]: 1791
% 1.38/0.58  % (20634)Time elapsed: 0.167 s
% 1.38/0.58  % (20634)------------------------------
% 1.38/0.58  % (20634)------------------------------
% 1.38/0.58  % (20624)Success in time 0.212 s
%------------------------------------------------------------------------------
