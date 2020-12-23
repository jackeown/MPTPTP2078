%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  64 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 355 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f18,f41,f56])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f41,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK3) ) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (18491)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (18489)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (18485)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (18489)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f20,f18,f41,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ~r1_xboole_0(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(resolution,[],[f25,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f14,f13,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK3)),
% 0.21/0.43    inference(resolution,[],[f39,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    r1_tarski(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK3)) )),
% 0.21/0.43    inference(superposition,[],[f30,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK2,sK3)),
% 0.21/0.43    inference(resolution,[],[f32,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    r1_xboole_0(sK3,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.43    inference(resolution,[],[f27,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (18489)------------------------------
% 0.21/0.43  % (18489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (18489)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (18489)Memory used [KB]: 6140
% 0.21/0.43  % (18489)Time elapsed: 0.025 s
% 0.21/0.43  % (18489)------------------------------
% 0.21/0.43  % (18489)------------------------------
% 0.21/0.43  % (18484)Success in time 0.075 s
%------------------------------------------------------------------------------
