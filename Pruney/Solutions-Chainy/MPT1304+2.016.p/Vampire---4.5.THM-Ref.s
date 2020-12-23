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
% DateTime   : Thu Dec  3 13:13:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 101 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 460 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f555])).

fof(f555,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f551,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f551,plain,(
    ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f544,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f544,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0) ) ),
    inference(resolution,[],[f537,f26])).

fof(f537,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ) ),
    inference(global_subsumption,[],[f23,f526])).

fof(f526,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
      | ~ v1_tops_2(sK1,sK0) ) ),
    inference(resolution,[],[f297,f21])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X1)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f156,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0) ) ),
    inference(global_subsumption,[],[f20,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f72,f31])).

fof(f31,plain,(
    ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f70,f31])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.45  % (26544)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.45  % (26546)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.46  % (26545)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.46  % (26543)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.50  % (26543)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f556,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(global_subsumption,[],[f21,f555])).
% 0.23/0.50  fof(f555,plain,(
% 0.23/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.50    inference(resolution,[],[f551,f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.50    inference(nnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.50  fof(f551,plain,(
% 0.23/0.50    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.50    inference(resolution,[],[f544,f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.50  fof(f544,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0)) )),
% 0.23/0.50    inference(resolution,[],[f537,f26])).
% 0.23/0.50  fof(f537,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1)) )),
% 0.23/0.50    inference(global_subsumption,[],[f23,f526])).
% 0.23/0.50  fof(f526,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~v1_tops_2(sK1,sK0)) )),
% 0.23/0.50    inference(resolution,[],[f297,f21])).
% 0.23/0.50  fof(f297,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X1) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~v1_tops_2(X0,sK0)) )),
% 0.23/0.50    inference(resolution,[],[f156,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.50    inference(flattening,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.50  fof(f156,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~v1_tops_2(X0,sK0)) )),
% 0.23/0.50    inference(resolution,[],[f74,f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f19])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,sK0) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0)) )),
% 0.23/0.50    inference(global_subsumption,[],[f20,f73])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.50    inference(forward_demodulation,[],[f72,f31])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.23/0.50    inference(resolution,[],[f29,f21])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.23/0.50  fof(f72,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.50    inference(forward_demodulation,[],[f70,f31])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_tops_2(X0,sK0) | ~r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.50    inference(resolution,[],[f25,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f9,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f8])).
% 0.23/0.51  fof(f8,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,negated_conjecture,(
% 0.23/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.23/0.51    inference(negated_conjecture,[],[f6])).
% 0.23/0.51  fof(f6,conjecture,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f10])).
% 0.23/0.51  fof(f10,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    l1_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    v1_tops_2(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (26543)------------------------------
% 0.23/0.51  % (26543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26543)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (26543)Memory used [KB]: 6524
% 0.23/0.51  % (26543)Time elapsed: 0.047 s
% 0.23/0.51  % (26543)------------------------------
% 0.23/0.51  % (26543)------------------------------
% 0.23/0.51  % (26538)Success in time 0.138 s
%------------------------------------------------------------------------------
