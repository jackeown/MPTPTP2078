%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 ( 319 expanded)
%              Number of equality atoms :   28 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f107,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f103,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f103,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f70])).

fof(f70,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f43,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f39,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f100,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(resolution,[],[f96,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f78,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),X0) ) ),
    inference(resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f77,plain,(
    ~ r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ~ m1_subset_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f37,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,
    ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f94,f68])).

fof(f68,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK0)
      | r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X12),sK0) ) ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f92,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK0)
      | r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X12),sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f64,f68])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:20:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (19447)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (19464)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (19444)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (19456)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (19451)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.51  % (19465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (19447)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(subsumption_resolution,[],[f107,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    k1_xboole_0 != sK0),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.19/0.52    inference(flattening,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.52    inference(negated_conjecture,[],[f17])).
% 0.19/0.52  fof(f17,conjecture,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.19/0.52  fof(f107,plain,(
% 0.19/0.52    k1_xboole_0 = sK0),
% 0.19/0.52    inference(resolution,[],[f103,f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    v1_xboole_0(sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f100,f70])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f69,f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,axiom,(
% 0.19/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(resolution,[],[f43,f67])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f39,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,axiom,(
% 0.19/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(nnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.52  fof(f100,plain,(
% 0.19/0.52    v1_xboole_0(sK0) | ~r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.19/0.52    inference(resolution,[],[f96,f83])).
% 0.19/0.52  fof(f83,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(resolution,[],[f78,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),X0)) )),
% 0.19/0.52    inference(resolution,[],[f77,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(rectify,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(nnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.52  fof(f77,plain,(
% 0.19/0.52    ~r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f76,f40])).
% 0.19/0.52  fof(f76,plain,(
% 0.19/0.52    ~r2_hidden(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(resolution,[],[f63,f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ~m1_subset_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(definition_unfolding,[],[f37,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f41,f61])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f55,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f56,f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f57,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK0) | v1_xboole_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f94,f68])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.19/0.52    inference(resolution,[],[f43,f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    m1_subset_1(sK1,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    ( ! [X12] : (~r2_hidden(X12,sK0) | r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X12),sK0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f92,f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    ( ! [X12] : (~r2_hidden(X12,sK0) | r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,X12),sK0) | v1_xboole_0(sK0)) )),
% 0.19/0.52    inference(resolution,[],[f64,f68])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 0.19/0.52    inference(definition_unfolding,[],[f49,f61])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.19/0.52    inference(flattening,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.19/0.52    inference(nnf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (19447)------------------------------
% 0.19/0.52  % (19447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (19447)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (19447)Memory used [KB]: 6268
% 0.19/0.52  % (19447)Time elapsed: 0.102 s
% 0.19/0.52  % (19447)------------------------------
% 0.19/0.52  % (19447)------------------------------
% 0.19/0.52  % (19457)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (19439)Success in time 0.163 s
%------------------------------------------------------------------------------
