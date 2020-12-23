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
% DateTime   : Thu Dec  3 13:13:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 220 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 510 expanded)
%              Number of equality atoms :   57 ( 211 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f104])).

fof(f104,plain,(
    ! [X0,X1] : sK1 != k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f46,f59,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66,plain,(
    ! [X0,X1] : sK1 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f45,f38,f62,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f136,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)))) ),
    inference(resolution,[],[f134,f93])).

fof(f93,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f35])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f42,f87])).

fof(f87,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    r1_tarski(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK1,X0)
      | r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f56,f64])).

fof(f64,plain,(
    sK1 = k3_tarski(sK1) ),
    inference(definition_unfolding,[],[f39,f38,f38])).

fof(f39,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f134,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)))) = X0 ) ),
    inference(forward_demodulation,[],[f133,f67])).

fof(f133,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f129,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f128,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))))) ),
    inference(definition_unfolding,[],[f51,f62,f61,f62])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k2_enumset1(X0,X0,X0,X0))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f62,f61,f63,f63])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

% (2282)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (2283)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (2286)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (2286)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % (2302)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.56  % (2294)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f137,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(subsumption_resolution,[],[f136,f104])).
% 1.39/0.56  fof(f104,plain,(
% 1.39/0.56    ( ! [X0,X1] : (sK1 != k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.39/0.56    inference(superposition,[],[f66,f67])).
% 1.39/0.56  fof(f67,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f46,f59,f59])).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f49,f58])).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.39/0.56  fof(f66,plain,(
% 1.39/0.56    ( ! [X0,X1] : (sK1 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f45,f38,f62,f63])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f41,f59])).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f48,f59])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    k1_xboole_0 = sK1),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25,f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f18])).
% 1.39/0.56  fof(f18,negated_conjecture,(
% 1.39/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.39/0.56    inference(negated_conjecture,[],[f17])).
% 1.39/0.56  fof(f17,conjecture,(
% 1.39/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f13])).
% 1.39/0.56  fof(f13,axiom,(
% 1.39/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.39/0.56  fof(f136,plain,(
% 1.39/0.56    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1))))),
% 1.39/0.56    inference(resolution,[],[f134,f93])).
% 1.39/0.56  fof(f93,plain,(
% 1.39/0.56    ~v1_xboole_0(sK1)),
% 1.39/0.56    inference(subsumption_resolution,[],[f92,f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ~v2_struct_0(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    ~v1_xboole_0(sK1) | v2_struct_0(sK0)),
% 1.39/0.56    inference(subsumption_resolution,[],[f91,f35])).
% 1.39/0.56  fof(f35,plain,(
% 1.39/0.56    l1_struct_0(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f91,plain,(
% 1.39/0.56    ~v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.39/0.56    inference(superposition,[],[f42,f87])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    u1_struct_0(sK0) = sK1),
% 1.39/0.56    inference(subsumption_resolution,[],[f86,f65])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f40,f38])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    u1_struct_0(sK0) = sK1 | ~r1_tarski(sK1,u1_struct_0(sK0))),
% 1.39/0.56    inference(resolution,[],[f55,f74])).
% 1.39/0.56  fof(f74,plain,(
% 1.39/0.56    r1_tarski(u1_struct_0(sK0),sK1)),
% 1.39/0.56    inference(resolution,[],[f73,f37])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_setfam_1(sK1,X0) | r1_tarski(X0,sK1)) )),
% 1.39/0.56    inference(superposition,[],[f56,f64])).
% 1.39/0.56  fof(f64,plain,(
% 1.39/0.56    sK1 = k3_tarski(sK1)),
% 1.39/0.56    inference(definition_unfolding,[],[f39,f38,f38])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.39/0.56    inference(cnf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f33])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f14])).
% 1.39/0.56  fof(f14,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.56    inference(flattening,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.56    inference(nnf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f16])).
% 1.39/0.56  fof(f16,axiom,(
% 1.39/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.39/0.56  fof(f134,plain,(
% 1.39/0.56    ( ! [X0] : (v1_xboole_0(X0) | k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)))) = X0) )),
% 1.39/0.56    inference(forward_demodulation,[],[f133,f67])).
% 1.39/0.56  fof(f133,plain,(
% 1.39/0.56    ( ! [X0] : (k3_tarski(k2_enumset1(k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),k2_enumset1(sK2(X0),sK2(X0),sK2(X0),sK2(X0)),X0)) = X0 | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(resolution,[],[f129,f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(rectify,[],[f27])).
% 1.39/0.56  fof(f27,plain,(
% 1.39/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.56  fof(f129,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1)) = X1) )),
% 1.39/0.56    inference(forward_demodulation,[],[f128,f68])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f51,f62,f61,f62])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f50,f60])).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f47,f59])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,axiom,(
% 1.39/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.39/0.56  fof(f128,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))))) = X1 | ~r2_hidden(X0,X1)) )),
% 1.39/0.56    inference(forward_demodulation,[],[f69,f67])).
% 1.39/0.56  fof(f69,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))),k2_enumset1(X0,X0,X0,X0))) = X1 | ~r2_hidden(X0,X1)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f52,f62,f61,f63,f63])).
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | ~r2_hidden(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  % (2282)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | ~r2_hidden(X0,X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (2286)------------------------------
% 1.39/0.56  % (2286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (2286)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (2286)Memory used [KB]: 10746
% 1.39/0.56  % (2286)Time elapsed: 0.121 s
% 1.39/0.56  % (2286)------------------------------
% 1.39/0.56  % (2286)------------------------------
% 1.39/0.57  % (2279)Success in time 0.205 s
%------------------------------------------------------------------------------
