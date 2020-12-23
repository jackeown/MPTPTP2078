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
% DateTime   : Thu Dec  3 13:07:17 EST 2020

% Result     : Theorem 6.34s
% Output     : Refutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   43 (  95 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 330 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8692,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8684,f1572])).

fof(f1572,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(sK0,X1)),k10_relat_1(sK0,X1)) ),
    inference(forward_demodulation,[],[f1514,f710])).

fof(f710,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f341,f518])).

fof(f518,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f214])).

fof(f214,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f341,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f113,f241,f240])).

fof(f240,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f241,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f108])).

fof(f108,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f107])).

fof(f107,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f1514,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f341,f685,f686,f478])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f686,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f341,f456])).

fof(f456,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f685,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f341,f455])).

fof(f455,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f8684,plain,(
    ~ r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f811,f863,f496])).

fof(f496,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f863,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f835,f341])).

fof(f835,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f344,f518])).

fof(f344,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f242])).

fof(f811,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f562,f343,f544])).

fof(f544,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f239])).

fof(f239,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f238])).

fof(f238,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f343,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f242])).

fof(f562,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f495])).

fof(f495,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (17688)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.48  % (17689)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.48  % (17681)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (17673)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (17696)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (17680)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (17676)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (17694)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (17671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (17672)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.54  % (17674)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.54  % (17670)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (17675)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (17669)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (17695)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (17686)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (17666)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.55  % (17687)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (17678)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (17677)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (17692)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.55  % (17685)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (17690)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.55  % (17679)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.56  % (17693)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.56  % (17682)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.56  % (17667)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.56  % (17684)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.57  % (17683)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.58  % (17691)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 3.55/0.84  % (17672)Time limit reached!
% 3.55/0.84  % (17672)------------------------------
% 3.55/0.84  % (17672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.84  % (17672)Termination reason: Time limit
% 3.55/0.84  % (17672)Termination phase: Saturation
% 3.55/0.84  
% 3.55/0.84  % (17672)Memory used [KB]: 9466
% 3.55/0.84  % (17672)Time elapsed: 0.400 s
% 3.55/0.84  % (17672)------------------------------
% 3.55/0.84  % (17672)------------------------------
% 3.83/0.91  % (17666)Time limit reached!
% 3.83/0.91  % (17666)------------------------------
% 3.83/0.91  % (17666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (17679)Time limit reached!
% 3.83/0.92  % (17679)------------------------------
% 3.83/0.92  % (17679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (17684)Time limit reached!
% 3.83/0.92  % (17684)------------------------------
% 3.83/0.92  % (17684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.93  % (17679)Termination reason: Time limit
% 3.83/0.93  
% 3.83/0.93  % (17679)Memory used [KB]: 9594
% 3.83/0.93  % (17679)Time elapsed: 0.508 s
% 3.83/0.93  % (17679)------------------------------
% 3.83/0.93  % (17679)------------------------------
% 4.42/0.93  % (17667)Time limit reached!
% 4.42/0.93  % (17667)------------------------------
% 4.42/0.93  % (17667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.93  % (17667)Termination reason: Time limit
% 4.42/0.93  % (17667)Termination phase: Saturation
% 4.42/0.93  
% 4.42/0.93  % (17667)Memory used [KB]: 8571
% 4.42/0.93  % (17667)Time elapsed: 0.500 s
% 4.42/0.93  % (17667)------------------------------
% 4.42/0.93  % (17667)------------------------------
% 4.42/0.93  % (17684)Termination reason: Time limit
% 4.42/0.93  
% 4.42/0.93  % (17684)Memory used [KB]: 14328
% 4.42/0.93  % (17684)Time elapsed: 0.523 s
% 4.42/0.93  % (17684)------------------------------
% 4.42/0.93  % (17684)------------------------------
% 4.42/0.93  % (17666)Termination reason: Time limit
% 4.42/0.93  % (17666)Termination phase: Saturation
% 4.42/0.93  
% 4.42/0.93  % (17666)Memory used [KB]: 3965
% 4.42/0.93  % (17666)Time elapsed: 0.500 s
% 4.42/0.93  % (17666)------------------------------
% 4.42/0.93  % (17666)------------------------------
% 4.42/0.94  % (17677)Time limit reached!
% 4.42/0.94  % (17677)------------------------------
% 4.42/0.94  % (17677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.95  % (17677)Termination reason: Time limit
% 4.42/0.95  
% 4.42/0.95  % (17677)Memory used [KB]: 14839
% 4.42/0.95  % (17677)Time elapsed: 0.529 s
% 4.42/0.95  % (17677)------------------------------
% 4.42/0.95  % (17677)------------------------------
% 4.42/0.97  % (17753)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.74/1.02  % (17695)Time limit reached!
% 4.74/1.02  % (17695)------------------------------
% 4.74/1.02  % (17695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.02  % (17695)Termination reason: Time limit
% 4.74/1.02  % (17695)Termination phase: Saturation
% 4.74/1.02  
% 4.74/1.02  % (17695)Memory used [KB]: 9466
% 4.74/1.02  % (17695)Time elapsed: 0.618 s
% 4.74/1.02  % (17695)------------------------------
% 4.74/1.02  % (17695)------------------------------
% 4.74/1.03  % (17683)Time limit reached!
% 4.74/1.03  % (17683)------------------------------
% 4.74/1.03  % (17683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (17683)Termination reason: Time limit
% 4.74/1.03  
% 4.74/1.03  % (17683)Memory used [KB]: 19317
% 4.74/1.03  % (17683)Time elapsed: 0.618 s
% 4.74/1.03  % (17683)------------------------------
% 4.74/1.03  % (17683)------------------------------
% 4.74/1.03  % (17674)Time limit reached!
% 4.74/1.03  % (17674)------------------------------
% 4.74/1.03  % (17674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.04  % (17674)Termination reason: Time limit
% 5.17/1.04  
% 5.17/1.04  % (17674)Memory used [KB]: 12281
% 5.17/1.04  % (17674)Time elapsed: 0.617 s
% 5.17/1.04  % (17674)------------------------------
% 5.17/1.04  % (17674)------------------------------
% 5.17/1.06  % (17757)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.17/1.06  % (17754)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.17/1.06  % (17755)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.17/1.07  % (17756)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.57/1.08  % (17758)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.06/1.16  % (17759)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.34/1.18  % (17693)Refutation found. Thanks to Tanya!
% 6.34/1.18  % SZS status Theorem for theBenchmark
% 6.34/1.18  % (17761)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.34/1.18  % SZS output start Proof for theBenchmark
% 6.34/1.18  fof(f8692,plain,(
% 6.34/1.18    $false),
% 6.34/1.18    inference(subsumption_resolution,[],[f8684,f1572])).
% 6.34/1.18  fof(f1572,plain,(
% 6.34/1.18    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK0,X1)),k10_relat_1(sK0,X1))) )),
% 6.34/1.18    inference(forward_demodulation,[],[f1514,f710])).
% 6.34/1.18  fof(f710,plain,(
% 6.34/1.18    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f341,f518])).
% 6.34/1.18  fof(f518,plain,(
% 6.34/1.18    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f214])).
% 6.34/1.18  fof(f214,plain,(
% 6.34/1.18    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 6.34/1.18    inference(ennf_transformation,[],[f88])).
% 6.34/1.18  fof(f88,axiom,(
% 6.34/1.18    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 6.34/1.18  fof(f341,plain,(
% 6.34/1.18    v1_relat_1(sK0)),
% 6.34/1.18    inference(cnf_transformation,[],[f242])).
% 6.34/1.18  fof(f242,plain,(
% 6.34/1.18    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 6.34/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f113,f241,f240])).
% 6.34/1.18  fof(f240,plain,(
% 6.34/1.18    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 6.34/1.18    introduced(choice_axiom,[])).
% 6.34/1.18  fof(f241,plain,(
% 6.34/1.18    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 6.34/1.18    introduced(choice_axiom,[])).
% 6.34/1.18  fof(f113,plain,(
% 6.34/1.18    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.34/1.18    inference(flattening,[],[f112])).
% 6.34/1.18  fof(f112,plain,(
% 6.34/1.18    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.34/1.18    inference(ennf_transformation,[],[f108])).
% 6.34/1.18  fof(f108,negated_conjecture,(
% 6.34/1.18    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 6.34/1.18    inference(negated_conjecture,[],[f107])).
% 6.34/1.18  fof(f107,conjecture,(
% 6.34/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 6.34/1.18  fof(f1514,plain,(
% 6.34/1.18    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k10_relat_1(sK0,X1))) )),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f341,f685,f686,f478])).
% 6.34/1.18  fof(f478,plain,(
% 6.34/1.18    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f189])).
% 6.34/1.18  fof(f189,plain,(
% 6.34/1.18    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 6.34/1.18    inference(flattening,[],[f188])).
% 6.34/1.18  fof(f188,plain,(
% 6.34/1.18    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 6.34/1.18    inference(ennf_transformation,[],[f51])).
% 6.34/1.18  fof(f51,axiom,(
% 6.34/1.18    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 6.34/1.18  fof(f686,plain,(
% 6.34/1.18    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0)) )),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f341,f456])).
% 6.34/1.18  fof(f456,plain,(
% 6.34/1.18    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f167])).
% 6.34/1.18  fof(f167,plain,(
% 6.34/1.18    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 6.34/1.18    inference(ennf_transformation,[],[f68])).
% 6.34/1.18  fof(f68,axiom,(
% 6.34/1.18    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 6.34/1.18  fof(f685,plain,(
% 6.34/1.18    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f341,f455])).
% 6.34/1.18  fof(f455,plain,(
% 6.34/1.18    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f166])).
% 6.34/1.18  fof(f166,plain,(
% 6.34/1.18    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 6.34/1.18    inference(ennf_transformation,[],[f24])).
% 6.34/1.18  fof(f24,axiom,(
% 6.34/1.18    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 6.34/1.18  fof(f8684,plain,(
% 6.34/1.18    ~r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f811,f863,f496])).
% 6.34/1.18  fof(f496,plain,(
% 6.34/1.18    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f317])).
% 6.34/1.18  fof(f317,plain,(
% 6.34/1.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.34/1.18    inference(flattening,[],[f316])).
% 6.34/1.18  fof(f316,plain,(
% 6.34/1.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.34/1.18    inference(nnf_transformation,[],[f4])).
% 6.34/1.18  fof(f4,axiom,(
% 6.34/1.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.34/1.18  fof(f863,plain,(
% 6.34/1.18    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 6.34/1.18    inference(subsumption_resolution,[],[f835,f341])).
% 6.34/1.18  fof(f835,plain,(
% 6.34/1.18    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 6.34/1.18    inference(superposition,[],[f344,f518])).
% 6.34/1.18  fof(f344,plain,(
% 6.34/1.18    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 6.34/1.18    inference(cnf_transformation,[],[f242])).
% 6.34/1.18  fof(f811,plain,(
% 6.34/1.18    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 6.34/1.18    inference(unit_resulting_resolution,[],[f562,f343,f544])).
% 6.34/1.18  fof(f544,plain,(
% 6.34/1.18    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.34/1.18    inference(cnf_transformation,[],[f239])).
% 6.34/1.18  fof(f239,plain,(
% 6.34/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 6.34/1.18    inference(flattening,[],[f238])).
% 6.34/1.18  fof(f238,plain,(
% 6.34/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 6.34/1.18    inference(ennf_transformation,[],[f9])).
% 6.34/1.18  fof(f9,axiom,(
% 6.34/1.18    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 6.34/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 6.34/1.18  fof(f343,plain,(
% 6.34/1.18    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 6.34/1.18    inference(cnf_transformation,[],[f242])).
% 6.34/1.18  fof(f562,plain,(
% 6.34/1.18    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.34/1.18    inference(equality_resolution,[],[f495])).
% 6.34/1.18  fof(f495,plain,(
% 6.34/1.18    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.34/1.18    inference(cnf_transformation,[],[f317])).
% 6.34/1.18  % SZS output end Proof for theBenchmark
% 6.34/1.18  % (17693)------------------------------
% 6.34/1.18  % (17693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.34/1.18  % (17693)Termination reason: Refutation
% 6.34/1.18  
% 6.34/1.18  % (17693)Memory used [KB]: 19317
% 6.34/1.18  % (17693)Time elapsed: 0.749 s
% 6.34/1.18  % (17693)------------------------------
% 6.34/1.18  % (17693)------------------------------
% 6.34/1.18  % (17760)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.34/1.19  % (17661)Success in time 0.821 s
%------------------------------------------------------------------------------
