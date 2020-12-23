%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 122 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 529 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f87,plain,(
    ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f80,f76])).

fof(f76,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f75,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

fof(f75,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f26,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f30,f56])).

fof(f56,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f80,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f77,f27])).

fof(f27,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,
    ( v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f31,f57])).

fof(f57,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f55,f49])).

fof(f55,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f46,f24])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (12495)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (12485)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (12489)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (12493)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (12503)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (12486)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (12484)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (12495)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f81,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f75,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    (~v3_tops_1(k2_tops_1(sK0,sK1),sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v3_tops_1(k2_tops_1(sK0,X1),sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X1] : (~v3_tops_1(k2_tops_1(sK0,X1),sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_tops_1(k2_tops_1(sK0,sK1),sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    v4_pre_topc(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(superposition,[],[f30,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f48,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f25,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(resolution,[],[f25,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f79,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f24])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f77,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    v3_tops_1(k2_tops_1(sK0,sK1),sK0) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.51    inference(superposition,[],[f31,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f55,f49])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f46,f24])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f25,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (12495)------------------------------
% 0.20/0.51  % (12495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12495)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (12495)Memory used [KB]: 1663
% 0.20/0.51  % (12495)Time elapsed: 0.081 s
% 0.20/0.51  % (12495)------------------------------
% 0.20/0.51  % (12495)------------------------------
% 0.20/0.51  % (12500)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (12483)Success in time 0.147 s
%------------------------------------------------------------------------------
