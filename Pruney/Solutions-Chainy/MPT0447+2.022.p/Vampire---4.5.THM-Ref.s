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
% DateTime   : Thu Dec  3 12:47:11 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 180 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   24
%              Number of atoms          :  178 ( 544 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f598,f95])).

fof(f95,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f51,f58])).

fof(f58,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f598,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f594,f27])).

fof(f594,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(resolution,[],[f585,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f585,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f578,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f578,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f576,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f576,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f575,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f575,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f573,f29])).

fof(f29,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f573,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f564,f518])).

fof(f518,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f514,f27])).

fof(f514,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f272,f28])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f268,f30])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f154,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(sK0),X3)
      | ~ r1_tarski(k1_relat_1(sK0),X2)
      | ~ r1_tarski(X3,X2)
      | r1_tarski(k3_relat_1(sK0),X2) ) ),
    inference(resolution,[],[f103,f48])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f52,f62])).

fof(f62,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f30,f50])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f564,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f562,f29])).

fof(f562,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(resolution,[],[f536,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f536,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k2_relat_1(sK1),X2),k3_relat_1(sK1))
      | r1_tarski(k3_relat_1(sK0),X2)
      | ~ r1_tarski(k1_relat_1(sK0),X2) ) ),
    inference(resolution,[],[f528,f90])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(X1,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | r2_hidden(X3,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f27,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f528,plain,(
    ! [X4] :
      ( r2_hidden(sK2(k2_relat_1(sK1),X4),k2_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK0),X4)
      | r1_tarski(k3_relat_1(sK0),X4) ) ),
    inference(resolution,[],[f518,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (28909)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (28916)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (28932)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (28922)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (28925)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.22/0.52  % (28915)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.52  % (28926)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (28906)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.52  % (28907)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.52  % (28918)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (28913)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.53  % (28930)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.53  % (28917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.53  % (28910)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.53  % (28904)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.53  % (28905)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.53  % (28927)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.53  % (28923)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.53  % (28924)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (28931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (28919)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.54  % (28908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.54  % (28933)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.54  % (28921)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.54  % (28911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.54  % (28921)Refutation not found, incomplete strategy% (28921)------------------------------
% 1.40/0.54  % (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (28921)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (28921)Memory used [KB]: 10618
% 1.40/0.54  % (28921)Time elapsed: 0.141 s
% 1.40/0.54  % (28921)------------------------------
% 1.40/0.54  % (28921)------------------------------
% 1.40/0.54  % (28914)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (28920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (28912)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (28928)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (28929)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.59  % (28925)Refutation found. Thanks to Tanya!
% 1.40/0.59  % SZS status Theorem for theBenchmark
% 1.40/0.59  % SZS output start Proof for theBenchmark
% 1.40/0.59  fof(f599,plain,(
% 1.40/0.59    $false),
% 1.40/0.59    inference(subsumption_resolution,[],[f598,f95])).
% 1.40/0.59  fof(f95,plain,(
% 1.40/0.59    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 1.40/0.59    inference(superposition,[],[f51,f58])).
% 1.40/0.59  fof(f58,plain,(
% 1.40/0.59    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 1.40/0.59    inference(resolution,[],[f27,f50])).
% 1.40/0.59  fof(f50,plain,(
% 1.40/0.59    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.40/0.59    inference(definition_unfolding,[],[f31,f36])).
% 1.40/0.59  fof(f36,plain,(
% 1.40/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f5])).
% 1.40/0.59  fof(f5,axiom,(
% 1.40/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.40/0.59  fof(f31,plain,(
% 1.40/0.59    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f16])).
% 1.40/0.59  fof(f16,plain,(
% 1.40/0.59    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f9])).
% 1.40/0.59  fof(f9,axiom,(
% 1.40/0.59    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.40/0.59  fof(f27,plain,(
% 1.40/0.59    v1_relat_1(sK1)),
% 1.40/0.59    inference(cnf_transformation,[],[f15])).
% 1.40/0.59  fof(f15,plain,(
% 1.40/0.59    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.40/0.59    inference(flattening,[],[f14])).
% 1.40/0.59  fof(f14,plain,(
% 1.40/0.59    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f13])).
% 1.40/0.59  fof(f13,negated_conjecture,(
% 1.40/0.59    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.40/0.59    inference(negated_conjecture,[],[f12])).
% 1.40/0.59  fof(f12,conjecture,(
% 1.40/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.40/0.59  fof(f51,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.40/0.59    inference(definition_unfolding,[],[f35,f36])).
% 1.40/0.59  fof(f35,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f3])).
% 1.40/0.59  fof(f3,axiom,(
% 1.40/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.40/0.59  fof(f598,plain,(
% 1.40/0.59    ~r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 1.40/0.59    inference(subsumption_resolution,[],[f594,f27])).
% 1.40/0.59  fof(f594,plain,(
% 1.40/0.59    ~v1_relat_1(sK1) | ~r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 1.40/0.59    inference(resolution,[],[f585,f28])).
% 1.40/0.59  fof(f28,plain,(
% 1.40/0.59    r1_tarski(sK0,sK1)),
% 1.40/0.59    inference(cnf_transformation,[],[f15])).
% 1.40/0.59  fof(f585,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))) )),
% 1.40/0.59    inference(subsumption_resolution,[],[f578,f30])).
% 1.40/0.59  fof(f30,plain,(
% 1.40/0.59    v1_relat_1(sK0)),
% 1.40/0.59    inference(cnf_transformation,[],[f15])).
% 1.40/0.59  fof(f578,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK0)) )),
% 1.40/0.59    inference(resolution,[],[f576,f32])).
% 1.40/0.59  fof(f32,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f18])).
% 1.40/0.59  fof(f18,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.59    inference(flattening,[],[f17])).
% 1.40/0.59  fof(f17,plain,(
% 1.40/0.59    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.59    inference(ennf_transformation,[],[f10])).
% 1.40/0.59  fof(f10,axiom,(
% 1.40/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.40/0.59  fof(f576,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(X0,k3_relat_1(sK1))) )),
% 1.40/0.59    inference(resolution,[],[f575,f48])).
% 1.40/0.59  fof(f48,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f24])).
% 1.40/0.59  fof(f24,plain,(
% 1.40/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.40/0.59    inference(flattening,[],[f23])).
% 1.40/0.59  fof(f23,plain,(
% 1.40/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.40/0.59    inference(ennf_transformation,[],[f2])).
% 1.40/0.59  fof(f2,axiom,(
% 1.40/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.40/0.59  fof(f575,plain,(
% 1.40/0.59    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.59    inference(subsumption_resolution,[],[f573,f29])).
% 1.40/0.59  fof(f29,plain,(
% 1.40/0.59    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.59    inference(cnf_transformation,[],[f15])).
% 1.40/0.59  fof(f573,plain,(
% 1.40/0.59    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.59    inference(duplicate_literal_removal,[],[f572])).
% 1.40/0.59  fof(f572,plain,(
% 1.40/0.59    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.59    inference(resolution,[],[f564,f518])).
% 1.40/0.59  fof(f518,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.40/0.59    inference(subsumption_resolution,[],[f514,f27])).
% 1.40/0.59  fof(f514,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~v1_relat_1(sK1) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.40/0.59    inference(resolution,[],[f272,f28])).
% 1.40/0.59  fof(f272,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.40/0.59    inference(subsumption_resolution,[],[f268,f30])).
% 1.40/0.59  fof(f268,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(X1),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | ~v1_relat_1(sK0)) )),
% 1.40/0.59    inference(resolution,[],[f154,f33])).
% 1.40/0.59  fof(f33,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f18])).
% 1.40/0.59  fof(f154,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(sK0),X3) | ~r1_tarski(k1_relat_1(sK0),X2) | ~r1_tarski(X3,X2) | r1_tarski(k3_relat_1(sK0),X2)) )),
% 1.40/0.59    inference(resolution,[],[f103,f48])).
% 1.40/0.59  fof(f103,plain,(
% 1.40/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.40/0.59    inference(superposition,[],[f52,f62])).
% 1.40/0.59  fof(f62,plain,(
% 1.40/0.59    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 1.40/0.59    inference(resolution,[],[f30,f50])).
% 1.40/0.59  fof(f52,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.59    inference(definition_unfolding,[],[f49,f36])).
% 1.40/0.59  fof(f49,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f26])).
% 1.40/0.59  fof(f26,plain,(
% 1.40/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.40/0.59    inference(flattening,[],[f25])).
% 1.40/0.59  fof(f25,plain,(
% 1.40/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.40/0.59    inference(ennf_transformation,[],[f4])).
% 1.40/0.59  fof(f4,axiom,(
% 1.40/0.59    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.40/0.59  fof(f564,plain,(
% 1.40/0.59    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.59    inference(subsumption_resolution,[],[f562,f29])).
% 1.40/0.59  fof(f562,plain,(
% 1.40/0.59    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))),
% 1.40/0.59    inference(resolution,[],[f536,f39])).
% 1.40/0.59  fof(f39,plain,(
% 1.40/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f20])).
% 1.40/0.59  fof(f20,plain,(
% 1.40/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.59    inference(ennf_transformation,[],[f1])).
% 1.40/0.59  fof(f1,axiom,(
% 1.40/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.59  fof(f536,plain,(
% 1.40/0.59    ( ! [X2] : (r2_hidden(sK2(k2_relat_1(sK1),X2),k3_relat_1(sK1)) | r1_tarski(k3_relat_1(sK0),X2) | ~r1_tarski(k1_relat_1(sK0),X2)) )),
% 1.40/0.59    inference(resolution,[],[f528,f90])).
% 1.40/0.59  fof(f90,plain,(
% 1.40/0.59    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(X1,k3_relat_1(sK1))) )),
% 1.40/0.59    inference(resolution,[],[f56,f53])).
% 1.40/0.59  fof(f53,plain,(
% 1.40/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.40/0.59    inference(equality_resolution,[],[f41])).
% 1.40/0.59  fof(f41,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.40/0.59    inference(cnf_transformation,[],[f8])).
% 1.40/0.59  fof(f8,axiom,(
% 1.40/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.40/0.59  fof(f56,plain,(
% 1.40/0.59    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | r2_hidden(X3,k3_relat_1(sK1))) )),
% 1.40/0.59    inference(resolution,[],[f27,f47])).
% 1.40/0.59  fof(f47,plain,(
% 1.40/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 1.40/0.59    inference(cnf_transformation,[],[f22])).
% 1.40/0.59  fof(f22,plain,(
% 1.40/0.59    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.40/0.59    inference(flattening,[],[f21])).
% 1.40/0.59  fof(f21,plain,(
% 1.40/0.59    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.40/0.59    inference(ennf_transformation,[],[f11])).
% 1.40/0.59  fof(f11,axiom,(
% 1.40/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.40/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 1.40/0.59  fof(f528,plain,(
% 1.40/0.59    ( ! [X4] : (r2_hidden(sK2(k2_relat_1(sK1),X4),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),X4) | r1_tarski(k3_relat_1(sK0),X4)) )),
% 1.40/0.59    inference(resolution,[],[f518,f38])).
% 1.40/0.59  fof(f38,plain,(
% 1.40/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.40/0.59    inference(cnf_transformation,[],[f20])).
% 1.40/0.59  % SZS output end Proof for theBenchmark
% 1.40/0.59  % (28925)------------------------------
% 1.40/0.59  % (28925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.59  % (28925)Termination reason: Refutation
% 1.40/0.59  
% 1.40/0.59  % (28925)Memory used [KB]: 2174
% 1.40/0.59  % (28925)Time elapsed: 0.190 s
% 1.40/0.59  % (28925)------------------------------
% 1.40/0.59  % (28925)------------------------------
% 1.40/0.60  % (28903)Success in time 0.237 s
%------------------------------------------------------------------------------
