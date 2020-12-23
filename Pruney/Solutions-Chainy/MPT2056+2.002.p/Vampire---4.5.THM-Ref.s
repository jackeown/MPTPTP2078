%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 320 expanded)
%              Number of leaves         :   23 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          :  349 (1505 expanded)
%              Number of equality atoms :   63 ( 266 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f664,plain,(
    $false ),
    inference(subsumption_resolution,[],[f663,f52])).

fof(f52,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f663,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f662,f351])).

fof(f351,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f95,f350])).

fof(f350,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f342,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f342,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f82,f78])).

fof(f82,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f67,f66,f73,f73])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f79,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f662,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f661,f509])).

fof(f509,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f444,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f444,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_tarski(X8))) ) ),
    inference(resolution,[],[f437,f130])).

fof(f130,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,X4)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k1_tarski(X5))) ) ),
    inference(resolution,[],[f102,f120])).

fof(f120,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,k1_tarski(X2))
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f115,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f106,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(k1_setfam_1(k2_tarski(X2,X3)))
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f66])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_setfam_1(k2_tarski(X1,X0)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f101,f65])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f66])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3)) ) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f437,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f436,f90])).

fof(f90,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f59,f87])).

fof(f87,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f436,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f435,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f435,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f434,f77])).

fof(f77,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f56,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f48,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f434,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f433,f76])).

fof(f76,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f49,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f433,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f432,f75])).

fof(f75,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f50,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f432,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f80,f74])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f56,f56,f56,f56])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f661,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tarski(k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f660,f226])).

fof(f226,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(resolution,[],[f85,f74])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f660,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f659,f45])).

fof(f659,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f658,f46])).

fof(f658,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f657,f47])).

fof(f657,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f656,f76])).

fof(f656,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f655,f75])).

fof(f655,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f81,f74])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f56,f56,f56,f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (23258)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.42  % (23258)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f664,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(subsumption_resolution,[],[f663,f52])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.19/0.42    inference(flattening,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,negated_conjecture,(
% 0.19/0.42    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.42    inference(negated_conjecture,[],[f18])).
% 0.19/0.42  fof(f18,conjecture,(
% 0.19/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.19/0.42  fof(f663,plain,(
% 0.19/0.42    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.42    inference(forward_demodulation,[],[f662,f351])).
% 0.19/0.42  fof(f351,plain,(
% 0.19/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(backward_demodulation,[],[f95,f350])).
% 0.19/0.42  fof(f350,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.19/0.42    inference(forward_demodulation,[],[f342,f78])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f54,f73])).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f68,f66])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.42  fof(f342,plain,(
% 0.19/0.42    ( ! [X0] : (k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)))) )),
% 0.19/0.42    inference(superposition,[],[f82,f78])).
% 0.19/0.42  fof(f82,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f67,f66,f73,f73])).
% 0.19/0.42  fof(f67,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) )),
% 0.19/0.42    inference(superposition,[],[f79,f65])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 0.19/0.42    inference(definition_unfolding,[],[f55,f73])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.42  fof(f662,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.19/0.42    inference(forward_demodulation,[],[f661,f509])).
% 0.19/0.42  fof(f509,plain,(
% 0.19/0.42    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_tarski(k1_xboole_0)))),
% 0.19/0.42    inference(resolution,[],[f444,f53])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.42  fof(f444,plain,(
% 0.19/0.42    ( ! [X8] : (~v1_xboole_0(X8) | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_tarski(X8)))) )),
% 0.19/0.42    inference(resolution,[],[f437,f130])).
% 0.19/0.42  fof(f130,plain,(
% 0.19/0.42    ( ! [X4,X5] : (r2_hidden(X5,X4) | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,k1_tarski(X5)))) )),
% 0.19/0.42    inference(resolution,[],[f102,f120])).
% 0.19/0.42  fof(f120,plain,(
% 0.19/0.42    ( ! [X2,X1] : (r1_xboole_0(X1,k1_tarski(X2)) | r2_hidden(X2,X1)) )),
% 0.19/0.42    inference(resolution,[],[f115,f71])).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f32])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,axiom,(
% 0.19/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.42  fof(f115,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(resolution,[],[f106,f109])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    ( ! [X2,X3] : (~v1_xboole_0(k1_setfam_1(k2_tarski(X2,X3))) | r1_xboole_0(X2,X3)) )),
% 0.19/0.42    inference(resolution,[],[f84,f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(rectify,[],[f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.42  fof(f84,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f69,f66])).
% 0.19/0.42  fof(f69,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f44])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(rectify,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.42  fof(f106,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_xboole_0(k1_setfam_1(k2_tarski(X1,X0))) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(superposition,[],[f101,f65])).
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_xboole_0(k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(resolution,[],[f83,f62])).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f40])).
% 0.19/0.42  fof(f83,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f70,f66])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f44])).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3))) )),
% 0.19/0.42    inference(resolution,[],[f83,f63])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f42])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ! [X0] : ((r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.19/0.42    inference(ennf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,axiom,(
% 0.19/0.42    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.19/0.42  fof(f437,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f436,f90])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.42    inference(subsumption_resolution,[],[f89,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ~v2_struct_0(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.19/0.42    inference(subsumption_resolution,[],[f88,f46])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    l1_struct_0(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.42    inference(superposition,[],[f59,f87])).
% 0.19/0.42  fof(f87,plain,(
% 0.19/0.42    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.19/0.42    inference(resolution,[],[f58,f46])).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,axiom,(
% 0.19/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.42    inference(flattening,[],[f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,axiom,(
% 0.19/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.42  fof(f436,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f435,f47])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ~v1_xboole_0(sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f435,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f434,f77])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.19/0.42    inference(definition_unfolding,[],[f48,f56])).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,axiom,(
% 0.19/0.42    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f434,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f433,f76])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.42    inference(definition_unfolding,[],[f49,f56])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f433,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.19/0.42    inference(subsumption_resolution,[],[f432,f75])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.42    inference(definition_unfolding,[],[f50,f56])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f432,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) )),
% 0.19/0.42    inference(resolution,[],[f80,f74])).
% 0.19/0.42  fof(f74,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.19/0.42    inference(definition_unfolding,[],[f51,f56])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.19/0.42    inference(cnf_transformation,[],[f36])).
% 0.19/0.42  fof(f80,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f57,f56,f56,f56,f56])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.42    inference(flattening,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,axiom,(
% 0.19/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.19/0.42  fof(f661,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tarski(k1_xboole_0))))),
% 0.19/0.42    inference(forward_demodulation,[],[f660,f226])).
% 0.19/0.42  fof(f226,plain,(
% 0.19/0.42    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 0.19/0.42    inference(resolution,[],[f85,f74])).
% 0.19/0.42  fof(f85,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f72,f73])).
% 0.19/0.42  fof(f72,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.42  fof(f660,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))),
% 0.19/0.42    inference(subsumption_resolution,[],[f659,f45])).
% 0.19/0.42  fof(f659,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | v2_struct_0(sK0)),
% 0.19/0.42    inference(subsumption_resolution,[],[f658,f46])).
% 0.19/0.42  fof(f658,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.42    inference(subsumption_resolution,[],[f657,f47])).
% 0.19/0.42  fof(f657,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.42    inference(subsumption_resolution,[],[f656,f76])).
% 0.19/0.42  fof(f656,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.42    inference(subsumption_resolution,[],[f655,f75])).
% 0.19/0.42  fof(f655,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.19/0.42    inference(resolution,[],[f81,f74])).
% 0.19/0.42  fof(f81,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f60,f56,f56,f56,f56])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.42    inference(flattening,[],[f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,axiom,(
% 0.19/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (23258)------------------------------
% 0.19/0.42  % (23258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (23258)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (23258)Memory used [KB]: 11001
% 0.19/0.42  % (23258)Time elapsed: 0.021 s
% 0.19/0.42  % (23258)------------------------------
% 0.19/0.42  % (23258)------------------------------
% 0.19/0.42  % (23247)Success in time 0.074 s
%------------------------------------------------------------------------------
