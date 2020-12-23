%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 383 expanded)
%              Number of leaves         :   13 ( 122 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 (1426 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1373,f1302])).

fof(f1302,plain,(
    r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f36,f1276])).

fof(f1276,plain,(
    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f1274,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1274,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f1271,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1271,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f36,f536])).

fof(f536,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f523,f430])).

fof(f430,plain,(
    sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f95,f55])).

fof(f55,plain,(
    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f32,f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
        & v5_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

fof(f32,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f30,f53,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f53,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f30,f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f523,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f93,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f93,plain,(
    m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f30,f53,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1373,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f1317,f536])).

fof(f1317,plain,(
    ! [X2] : ~ r1_tarski(k2_xboole_0(X2,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK1) ),
    inference(superposition,[],[f320,f313])).

fof(f313,plain,(
    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f121,f35])).

fof(f121,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f119,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f37,f55])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(f320,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(X1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)),sK1) ),
    inference(superposition,[],[f124,f44])).

fof(f124,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(k2_tops_1(sK0,sK1),X0),X1),sK1) ),
    inference(unit_resulting_resolution,[],[f122,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f122,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k2_tops_1(sK0,sK1),X0),sK1) ),
    inference(unit_resulting_resolution,[],[f116,f34])).

fof(f116,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f33,f55])).

fof(f33,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (9673)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (9670)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (9672)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (9672)Refutation not found, incomplete strategy% (9672)------------------------------
% 0.20/0.50  % (9672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9671)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (9688)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (9672)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9672)Memory used [KB]: 10490
% 0.20/0.51  % (9672)Time elapsed: 0.084 s
% 0.20/0.51  % (9672)------------------------------
% 0.20/0.51  % (9672)------------------------------
% 0.20/0.51  % (9682)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (9686)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (9680)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (9675)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (9669)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (9674)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (9690)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.52  % (9687)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (9679)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (9692)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (9678)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (9691)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.52  % (9689)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (9684)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.53  % (9683)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.53  % (9681)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.53  % (9677)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.53  % (9685)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.53  % (9676)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (9686)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f1375,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(subsumption_resolution,[],[f1373,f1302])).
% 1.60/0.58  fof(f1302,plain,(
% 1.60/0.58    r1_tarski(sK1,sK1)),
% 1.60/0.58    inference(superposition,[],[f36,f1276])).
% 1.60/0.58  fof(f1276,plain,(
% 1.60/0.58    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.60/0.58    inference(superposition,[],[f1274,f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.60/0.58  fof(f1274,plain,(
% 1.60/0.58    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f1271,f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,plain,(
% 1.60/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.60/0.58  fof(f1271,plain,(
% 1.60/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.60/0.58    inference(superposition,[],[f36,f536])).
% 1.60/0.58  fof(f536,plain,(
% 1.60/0.58    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(forward_demodulation,[],[f523,f430])).
% 1.60/0.58  fof(f430,plain,(
% 1.60/0.58    sK1 = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(forward_demodulation,[],[f95,f55])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f30,f32,f31,f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f29])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(nnf_transformation,[],[f18])).
% 1.60/0.58  fof(f18,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f14,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.60/0.58    inference(flattening,[],[f13])).
% 1.60/0.58  fof(f13,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,negated_conjecture,(
% 1.60/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 1.60/0.58    inference(negated_conjecture,[],[f11])).
% 1.60/0.58  fof(f11,conjecture,(
% 1.60/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    v5_tops_1(sK1,sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    l1_pre_topc(sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f95,plain,(
% 1.60/0.58    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f30,f53,f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f9])).
% 1.60/0.58  fof(f9,axiom,(
% 1.60/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f30,f31,f41])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f21])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(flattening,[],[f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.60/0.58  fof(f523,plain,(
% 1.60/0.58    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f93,f109])).
% 1.60/0.58  fof(f109,plain,(
% 1.60/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k2_xboole_0(k1_tops_1(sK0,sK1),X0)) )),
% 1.60/0.58    inference(resolution,[],[f53,f43])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.58    inference(flattening,[],[f24])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.60/0.58    inference(ennf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.60/0.58  fof(f93,plain,(
% 1.60/0.58    m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f30,f53,f42])).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f23])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(flattening,[],[f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.58  fof(f1373,plain,(
% 1.60/0.58    ~r1_tarski(sK1,sK1)),
% 1.60/0.58    inference(superposition,[],[f1317,f536])).
% 1.60/0.58  fof(f1317,plain,(
% 1.60/0.58    ( ! [X2] : (~r1_tarski(k2_xboole_0(X2,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK1)) )),
% 1.60/0.58    inference(superposition,[],[f320,f313])).
% 1.60/0.58  fof(f313,plain,(
% 1.60/0.58    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f121,f35])).
% 1.60/0.58  fof(f121,plain,(
% 1.60/0.58    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(subsumption_resolution,[],[f120,f30])).
% 1.60/0.58  fof(f120,plain,(
% 1.60/0.58    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 1.60/0.58    inference(subsumption_resolution,[],[f119,f53])).
% 1.60/0.58  fof(f119,plain,(
% 1.60/0.58    r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.60/0.58    inference(superposition,[],[f37,f55])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).
% 1.60/0.58  fof(f320,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)),sK1)) )),
% 1.60/0.58    inference(superposition,[],[f124,f44])).
% 1.60/0.58  fof(f124,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(k2_tops_1(sK0,sK1),X0),X1),sK1)) )),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f122,f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.60/0.58  fof(f15,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.60/0.58    inference(ennf_transformation,[],[f2])).
% 1.60/0.58  fof(f2,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.60/0.58  fof(f122,plain,(
% 1.60/0.58    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_tops_1(sK0,sK1),X0),sK1)) )),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f116,f34])).
% 1.60/0.58  fof(f116,plain,(
% 1.60/0.58    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.60/0.58    inference(backward_demodulation,[],[f33,f55])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (9686)------------------------------
% 1.60/0.58  % (9686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (9686)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (9686)Memory used [KB]: 2174
% 1.60/0.58  % (9686)Time elapsed: 0.124 s
% 1.60/0.58  % (9686)------------------------------
% 1.60/0.58  % (9686)------------------------------
% 1.60/0.58  % (9668)Success in time 0.219 s
%------------------------------------------------------------------------------
