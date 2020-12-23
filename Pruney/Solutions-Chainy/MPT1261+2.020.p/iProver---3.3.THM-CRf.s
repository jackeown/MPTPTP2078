%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:28 EST 2020

% Result     : Theorem 15.45s
% Output     : CNFRefutation 15.45s
% Verified   : 
% Statistics : Number of formulae       :  162 (1452 expanded)
%              Number of clauses        :   88 ( 415 expanded)
%              Number of leaves         :   21 ( 345 expanded)
%              Depth                    :   23
%              Number of atoms          :  376 (4824 expanded)
%              Number of equality atoms :  191 (1789 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f86,f104])).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f89,f119])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f142,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f102,f119])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK4,k1_tops_1(X0,sK4)) != k2_tops_1(X0,sK4)
          | ~ v4_pre_topc(sK4,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK4,k1_tops_1(X0,sK4)) = k2_tops_1(X0,sK4)
          | v4_pre_topc(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK3),X1,k1_tops_1(sK3,X1)) != k2_tops_1(sK3,X1)
            | ~ v4_pre_topc(X1,sK3) )
          & ( k7_subset_1(u1_struct_0(sK3),X1,k1_tops_1(sK3,X1)) = k2_tops_1(sK3,X1)
            | v4_pre_topc(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
      | ~ v4_pre_topc(sK4,sK3) )
    & ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
      | v4_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f67,f69,f68])).

fof(f116,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f103,f119])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f117,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f138,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f93,f96,f104,f119])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f139,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f94,f96,f96,f96])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f101,f96])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ) ),
    inference(definition_unfolding,[],[f92,f96,f119])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f97,f119])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
    | ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1367,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1402,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1367,c_29])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1352,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1362,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3491,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1362])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_281,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_30,c_282])).

cnf(c_1345,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_1460,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1345,c_29])).

cnf(c_4740,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,X0) = k6_subset_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3491,c_1460])).

cnf(c_41,negated_conjecture,
    ( v4_pre_topc(sK4,sK3)
    | k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1353,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5522,plain,
    ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4740,c_1353])).

cnf(c_35,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1359,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21362,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | v4_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1359])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_46,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_21741,plain,
    ( v4_pre_topc(sK4,sK3) != iProver_top
    | k2_pre_topc(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21362,c_46])).

cnf(c_21742,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_21741])).

cnf(c_21747,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5522,c_21742])).

cnf(c_23,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_21,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1427,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_21,c_29])).

cnf(c_2557,plain,
    ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_23,c_1427])).

cnf(c_22,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2586,plain,
    ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_2557,c_22])).

cnf(c_2587,plain,
    ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2586,c_2557])).

cnf(c_2677,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_23,c_2587])).

cnf(c_22609,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = sK4 ),
    inference(superposition,[status(thm)],[c_21747,c_2677])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1356,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_20990,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k2_pre_topc(sK3,sK4)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1356])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_282])).

cnf(c_1346,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_2420,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1346])).

cnf(c_6669,plain,
    ( k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4)))
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_2420])).

cnf(c_7362,plain,
    ( r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6669,c_46])).

cnf(c_7363,plain,
    ( k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4)))
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7362])).

cnf(c_7371,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_3491,c_7363])).

cnf(c_21003,plain,
    ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = k2_pre_topc(sK3,sK4)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20990,c_7371])).

cnf(c_22164,plain,
    ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = k2_pre_topc(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21003,c_46])).

cnf(c_22652,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_22609,c_22164])).

cnf(c_22655,plain,
    ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = sK4 ),
    inference(demodulation,[status(thm)],[c_22652,c_22164])).

cnf(c_20,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1365,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1480,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1365,c_29])).

cnf(c_23698,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r1_tarski(k6_subset_1(X0,sK4),k2_tops_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22655,c_1480])).

cnf(c_50781,plain,
    ( r1_tarski(k2_tops_1(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_23698])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_24,c_282])).

cnf(c_1349,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1446,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1349,c_29])).

cnf(c_51525,plain,
    ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k3_subset_1(sK4,k2_tops_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_50781,c_1446])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1355,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_19416,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1355])).

cnf(c_19431,plain,
    ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19416,c_4740])).

cnf(c_19774,plain,
    ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19431,c_46])).

cnf(c_51533,plain,
    ( k3_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_51525,c_19774])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_360,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_27,c_282])).

cnf(c_1347,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_51527,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK4,k2_tops_1(sK3,sK4))) = k2_tops_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_50781,c_1347])).

cnf(c_51534,plain,
    ( k3_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_51533,c_51527])).

cnf(c_19788,plain,
    ( r1_tarski(k1_tops_1(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19774,c_1402])).

cnf(c_19864,plain,
    ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k3_subset_1(sK4,k1_tops_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_19788,c_1446])).

cnf(c_40,negated_conjecture,
    ( ~ v4_pre_topc(sK4,sK3)
    | k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1354,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5523,plain,
    ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4740,c_1354])).

cnf(c_41621,plain,
    ( k3_subset_1(sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
    | v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19864,c_5523])).

cnf(c_34,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_11076,plain,
    ( v4_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | k2_pre_topc(sK3,sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_11077,plain,
    ( k2_pre_topc(sK3,sK4) != sK4
    | v4_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11076])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_45,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51534,c_41621,c_22652,c_11077,c_47,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.45/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.45/2.49  
% 15.45/2.49  ------  iProver source info
% 15.45/2.49  
% 15.45/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.45/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.45/2.49  git: non_committed_changes: false
% 15.45/2.49  git: last_make_outside_of_git: false
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  ------ Parsing...
% 15.45/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.45/2.49  ------ Proving...
% 15.45/2.49  ------ Problem Properties 
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  clauses                                 45
% 15.45/2.49  conjectures                             5
% 15.45/2.49  EPR                                     4
% 15.45/2.49  Horn                                    37
% 15.45/2.49  unary                                   12
% 15.45/2.49  binary                                  17
% 15.45/2.49  lits                                    99
% 15.45/2.49  lits eq                                 24
% 15.45/2.49  fd_pure                                 0
% 15.45/2.49  fd_pseudo                               0
% 15.45/2.49  fd_cond                                 0
% 15.45/2.49  fd_pseudo_cond                          6
% 15.45/2.49  AC symbols                              0
% 15.45/2.49  
% 15.45/2.49  ------ Input Options Time Limit: Unbounded
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  Current options:
% 15.45/2.49  ------ 
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ Proving...
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  % SZS status Theorem for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  fof(f7,axiom,(
% 15.45/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f89,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f7])).
% 15.45/2.49  
% 15.45/2.49  fof(f4,axiom,(
% 15.45/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f86,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f4])).
% 15.45/2.49  
% 15.45/2.49  fof(f22,axiom,(
% 15.45/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f104,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f22])).
% 15.45/2.49  
% 15.45/2.49  fof(f119,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f86,f104])).
% 15.45/2.49  
% 15.45/2.49  fof(f134,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f89,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f20,axiom,(
% 15.45/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f102,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f20])).
% 15.45/2.49  
% 15.45/2.49  fof(f142,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f102,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f30,conjecture,(
% 15.45/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f31,negated_conjecture,(
% 15.45/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 15.45/2.49    inference(negated_conjecture,[],[f30])).
% 15.45/2.49  
% 15.45/2.49  fof(f49,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f31])).
% 15.45/2.49  
% 15.45/2.49  fof(f50,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.45/2.49    inference(flattening,[],[f49])).
% 15.45/2.49  
% 15.45/2.49  fof(f66,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.45/2.49    inference(nnf_transformation,[],[f50])).
% 15.45/2.49  
% 15.45/2.49  fof(f67,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.45/2.49    inference(flattening,[],[f66])).
% 15.45/2.49  
% 15.45/2.49  fof(f69,plain,(
% 15.45/2.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK4,k1_tops_1(X0,sK4)) != k2_tops_1(X0,sK4) | ~v4_pre_topc(sK4,X0)) & (k7_subset_1(u1_struct_0(X0),sK4,k1_tops_1(X0,sK4)) = k2_tops_1(X0,sK4) | v4_pre_topc(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f68,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK3),X1,k1_tops_1(sK3,X1)) != k2_tops_1(sK3,X1) | ~v4_pre_topc(X1,sK3)) & (k7_subset_1(u1_struct_0(sK3),X1,k1_tops_1(sK3,X1)) = k2_tops_1(sK3,X1) | v4_pre_topc(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f70,plain,(
% 15.45/2.49    ((k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4) | ~v4_pre_topc(sK4,sK3)) & (k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) | v4_pre_topc(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f67,f69,f68])).
% 15.45/2.49  
% 15.45/2.49  fof(f116,plain,(
% 15.45/2.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 15.45/2.49    inference(cnf_transformation,[],[f70])).
% 15.45/2.49  
% 15.45/2.49  fof(f23,axiom,(
% 15.45/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f65,plain,(
% 15.45/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.45/2.49    inference(nnf_transformation,[],[f23])).
% 15.45/2.49  
% 15.45/2.49  fof(f105,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f65])).
% 15.45/2.49  
% 15.45/2.49  fof(f21,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f40,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f21])).
% 15.45/2.49  
% 15.45/2.49  fof(f103,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f143,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f103,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f106,plain,(
% 15.45/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f65])).
% 15.45/2.49  
% 15.45/2.49  fof(f117,plain,(
% 15.45/2.49    k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) | v4_pre_topc(sK4,sK3)),
% 15.45/2.49    inference(cnf_transformation,[],[f70])).
% 15.45/2.49  
% 15.45/2.49  fof(f25,axiom,(
% 15.45/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f42,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f25])).
% 15.45/2.49  
% 15.45/2.49  fof(f43,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.45/2.49    inference(flattening,[],[f42])).
% 15.45/2.49  
% 15.45/2.49  fof(f108,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f43])).
% 15.45/2.49  
% 15.45/2.49  fof(f115,plain,(
% 15.45/2.49    l1_pre_topc(sK3)),
% 15.45/2.49    inference(cnf_transformation,[],[f70])).
% 15.45/2.49  
% 15.45/2.49  fof(f13,axiom,(
% 15.45/2.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f95,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f13])).
% 15.45/2.49  
% 15.45/2.49  fof(f11,axiom,(
% 15.45/2.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f93,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 15.45/2.49    inference(cnf_transformation,[],[f11])).
% 15.45/2.49  
% 15.45/2.49  fof(f14,axiom,(
% 15.45/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f96,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f14])).
% 15.45/2.49  
% 15.45/2.49  fof(f138,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 15.45/2.49    inference(definition_unfolding,[],[f93,f96,f104,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f12,axiom,(
% 15.45/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f94,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f12])).
% 15.45/2.49  
% 15.45/2.49  fof(f139,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f94,f96,f96,f96])).
% 15.45/2.49  
% 15.45/2.49  fof(f28,axiom,(
% 15.45/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f47,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f28])).
% 15.45/2.49  
% 15.45/2.49  fof(f112,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f47])).
% 15.45/2.49  
% 15.45/2.49  fof(f26,axiom,(
% 15.45/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f44,plain,(
% 15.45/2.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f26])).
% 15.45/2.49  
% 15.45/2.49  fof(f45,plain,(
% 15.45/2.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.45/2.49    inference(flattening,[],[f44])).
% 15.45/2.49  
% 15.45/2.49  fof(f110,plain,(
% 15.45/2.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f45])).
% 15.45/2.49  
% 15.45/2.49  fof(f19,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f38,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.45/2.49    inference(ennf_transformation,[],[f19])).
% 15.45/2.49  
% 15.45/2.49  fof(f39,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.45/2.49    inference(flattening,[],[f38])).
% 15.45/2.49  
% 15.45/2.49  fof(f101,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f39])).
% 15.45/2.49  
% 15.45/2.49  fof(f141,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f101,f96])).
% 15.45/2.49  
% 15.45/2.49  fof(f10,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f34,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.45/2.49    inference(ennf_transformation,[],[f10])).
% 15.45/2.49  
% 15.45/2.49  fof(f92,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f34])).
% 15.45/2.49  
% 15.45/2.49  fof(f137,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f92,f96,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f15,axiom,(
% 15.45/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f35,plain,(
% 15.45/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f15])).
% 15.45/2.49  
% 15.45/2.49  fof(f97,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f35])).
% 15.45/2.49  
% 15.45/2.49  fof(f140,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f97,f119])).
% 15.45/2.49  
% 15.45/2.49  fof(f29,axiom,(
% 15.45/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f48,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f29])).
% 15.45/2.49  
% 15.45/2.49  fof(f113,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f48])).
% 15.45/2.49  
% 15.45/2.49  fof(f18,axiom,(
% 15.45/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f37,plain,(
% 15.45/2.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f18])).
% 15.45/2.49  
% 15.45/2.49  fof(f100,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f37])).
% 15.45/2.49  
% 15.45/2.49  fof(f118,plain,(
% 15.45/2.49    k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4) | ~v4_pre_topc(sK4,sK3)),
% 15.45/2.49    inference(cnf_transformation,[],[f70])).
% 15.45/2.49  
% 15.45/2.49  fof(f109,plain,(
% 15.45/2.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f43])).
% 15.45/2.49  
% 15.45/2.49  fof(f114,plain,(
% 15.45/2.49    v2_pre_topc(sK3)),
% 15.45/2.49    inference(cnf_transformation,[],[f70])).
% 15.45/2.49  
% 15.45/2.49  cnf(c_17,plain,
% 15.45/2.49      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f134]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1367,plain,
% 15.45/2.49      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_29,plain,
% 15.45/2.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f142]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1402,plain,
% 15.45/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 15.45/2.49      inference(light_normalisation,[status(thm)],[c_1367,c_29]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_42,negated_conjecture,
% 15.45/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 15.45/2.49      inference(cnf_transformation,[],[f116]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1352,plain,
% 15.45/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_32,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1362,plain,
% 15.45/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3491,plain,
% 15.45/2.49      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1352,c_1362]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_30,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.45/2.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f143]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_31,plain,
% 15.45/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_281,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.45/2.49      inference(prop_impl,[status(thm)],[c_31]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_282,plain,
% 15.45/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.45/2.49      inference(renaming,[status(thm)],[c_281]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_362,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1)
% 15.45/2.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 15.45/2.49      inference(bin_hyper_res,[status(thm)],[c_30,c_282]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1345,plain,
% 15.45/2.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 15.45/2.49      | r1_tarski(X0,X2) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1460,plain,
% 15.45/2.49      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 15.45/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.45/2.50      inference(light_normalisation,[status(thm)],[c_1345,c_29]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_4740,plain,
% 15.45/2.50      ( k7_subset_1(u1_struct_0(sK3),sK4,X0) = k6_subset_1(sK4,X0) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_3491,c_1460]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_41,negated_conjecture,
% 15.45/2.50      ( v4_pre_topc(sK4,sK3)
% 15.45/2.50      | k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(cnf_transformation,[],[f117]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1353,plain,
% 15.45/2.50      ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
% 15.45/2.50      | v4_pre_topc(sK4,sK3) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_5522,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4)
% 15.45/2.50      | v4_pre_topc(sK4,sK3) = iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_4740,c_1353]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_35,plain,
% 15.45/2.50      ( ~ v4_pre_topc(X0,X1)
% 15.45/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | ~ l1_pre_topc(X1)
% 15.45/2.50      | k2_pre_topc(X1,X0) = X0 ),
% 15.45/2.50      inference(cnf_transformation,[],[f108]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1359,plain,
% 15.45/2.50      ( k2_pre_topc(X0,X1) = X1
% 15.45/2.50      | v4_pre_topc(X1,X0) != iProver_top
% 15.45/2.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.45/2.50      | l1_pre_topc(X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21362,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) = sK4
% 15.45/2.50      | v4_pre_topc(sK4,sK3) != iProver_top
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1352,c_1359]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_43,negated_conjecture,
% 15.45/2.50      ( l1_pre_topc(sK3) ),
% 15.45/2.50      inference(cnf_transformation,[],[f115]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_46,plain,
% 15.45/2.50      ( l1_pre_topc(sK3) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21741,plain,
% 15.45/2.50      ( v4_pre_topc(sK4,sK3) != iProver_top
% 15.45/2.50      | k2_pre_topc(sK3,sK4) = sK4 ),
% 15.45/2.50      inference(global_propositional_subsumption,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_21362,c_46]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21742,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) = sK4
% 15.45/2.50      | v4_pre_topc(sK4,sK3) != iProver_top ),
% 15.45/2.50      inference(renaming,[status(thm)],[c_21741]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21747,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) = sK4
% 15.45/2.50      | k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_5522,c_21742]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_23,plain,
% 15.45/2.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 15.45/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 15.45/2.50      inference(cnf_transformation,[],[f138]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1427,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
% 15.45/2.50      inference(light_normalisation,[status(thm)],[c_21,c_29]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_2557,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_23,c_1427]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_22,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 15.45/2.50      inference(cnf_transformation,[],[f139]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_2586,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_2557,c_22]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_2587,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) = X0 ),
% 15.45/2.50      inference(light_normalisation,[status(thm)],[c_2586,c_2557]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_2677,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_23,c_2587]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_22609,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) = sK4
% 15.45/2.50      | k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = sK4 ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_21747,c_2677]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_38,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | ~ l1_pre_topc(X1)
% 15.45/2.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 15.45/2.50      inference(cnf_transformation,[],[f112]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1356,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 15.45/2.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.45/2.50      | l1_pre_topc(X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_20990,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k2_pre_topc(sK3,sK4)
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1352,c_1356]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_36,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | ~ l1_pre_topc(X1) ),
% 15.45/2.50      inference(cnf_transformation,[],[f110]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1358,plain,
% 15.45/2.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.45/2.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.45/2.50      | l1_pre_topc(X1) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_28,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.45/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.45/2.50      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 15.45/2.50      inference(cnf_transformation,[],[f141]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_361,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.45/2.50      | ~ r1_tarski(X2,X1)
% 15.45/2.50      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 15.45/2.50      inference(bin_hyper_res,[status(thm)],[c_28,c_282]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1346,plain,
% 15.45/2.50      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 15.45/2.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 15.45/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_2420,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
% 15.45/2.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.45/2.50      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 15.45/2.50      | l1_pre_topc(X0) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1358,c_1346]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_6669,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4)))
% 15.45/2.50      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1352,c_2420]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_7362,plain,
% 15.45/2.50      ( r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 15.45/2.50      | k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4))) ),
% 15.45/2.50      inference(global_propositional_subsumption,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_6669,c_46]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_7363,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK3,sK4)))
% 15.45/2.50      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 15.45/2.50      inference(renaming,[status(thm)],[c_7362]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_7371,plain,
% 15.45/2.50      ( k4_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_3491,c_7363]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_21003,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = k2_pre_topc(sK3,sK4)
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_20990,c_7371]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_22164,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = k2_pre_topc(sK3,sK4) ),
% 15.45/2.50      inference(global_propositional_subsumption,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_21003,c_46]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_22652,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_22609,c_22164]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_22655,plain,
% 15.45/2.50      ( k3_tarski(k2_tarski(sK4,k2_tops_1(sK3,sK4))) = sK4 ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_22652,c_22164]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_20,plain,
% 15.45/2.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 15.45/2.50      | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) ),
% 15.45/2.50      inference(cnf_transformation,[],[f137]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1365,plain,
% 15.45/2.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 15.45/2.50      | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1480,plain,
% 15.45/2.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 15.45/2.50      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 15.45/2.50      inference(light_normalisation,[status(thm)],[c_1365,c_29]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_23698,plain,
% 15.45/2.50      ( r1_tarski(X0,sK4) = iProver_top
% 15.45/2.50      | r1_tarski(k6_subset_1(X0,sK4),k2_tops_1(sK3,sK4)) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_22655,c_1480]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_50781,plain,
% 15.45/2.50      ( r1_tarski(k2_tops_1(sK3,sK4),sK4) = iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1402,c_23698]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_24,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.45/2.50      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 15.45/2.50      inference(cnf_transformation,[],[f140]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_358,plain,
% 15.45/2.50      ( ~ r1_tarski(X0,X1)
% 15.45/2.50      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 15.45/2.50      inference(bin_hyper_res,[status(thm)],[c_24,c_282]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1349,plain,
% 15.45/2.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 15.45/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1446,plain,
% 15.45/2.50      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 15.45/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_1349,c_29]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_51525,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k3_subset_1(sK4,k2_tops_1(sK3,sK4)) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_50781,c_1446]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_39,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | ~ l1_pre_topc(X1)
% 15.45/2.50      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 15.45/2.50      inference(cnf_transformation,[],[f113]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1355,plain,
% 15.45/2.50      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 15.45/2.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.45/2.50      | l1_pre_topc(X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19416,plain,
% 15.45/2.50      ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4)
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1352,c_1355]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19431,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4)
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_19416,c_4740]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19774,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(global_propositional_subsumption,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_19431,c_46]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_51533,plain,
% 15.45/2.50      ( k3_subset_1(sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(light_normalisation,[status(thm)],[c_51525,c_19774]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_27,plain,
% 15.45/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.45/2.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.45/2.50      inference(cnf_transformation,[],[f100]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_360,plain,
% 15.45/2.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.45/2.50      inference(bin_hyper_res,[status(thm)],[c_27,c_282]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1347,plain,
% 15.45/2.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.45/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_51527,plain,
% 15.45/2.50      ( k3_subset_1(sK4,k3_subset_1(sK4,k2_tops_1(sK3,sK4))) = k2_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_50781,c_1347]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_51534,plain,
% 15.45/2.50      ( k3_subset_1(sK4,k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_51533,c_51527]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19788,plain,
% 15.45/2.50      ( r1_tarski(k1_tops_1(sK3,sK4),sK4) = iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_19774,c_1402]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19864,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) = k3_subset_1(sK4,k1_tops_1(sK3,sK4)) ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_19788,c_1446]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_40,negated_conjecture,
% 15.45/2.50      ( ~ v4_pre_topc(sK4,sK3)
% 15.45/2.50      | k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4) ),
% 15.45/2.50      inference(cnf_transformation,[],[f118]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1354,plain,
% 15.45/2.50      ( k7_subset_1(u1_struct_0(sK3),sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
% 15.45/2.50      | v4_pre_topc(sK4,sK3) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_5523,plain,
% 15.45/2.50      ( k6_subset_1(sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
% 15.45/2.50      | v4_pre_topc(sK4,sK3) != iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_4740,c_1354]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_41621,plain,
% 15.45/2.50      ( k3_subset_1(sK4,k1_tops_1(sK3,sK4)) != k2_tops_1(sK3,sK4)
% 15.45/2.50      | v4_pre_topc(sK4,sK3) != iProver_top ),
% 15.45/2.50      inference(demodulation,[status(thm)],[c_19864,c_5523]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_34,plain,
% 15.45/2.50      ( v4_pre_topc(X0,X1)
% 15.45/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.50      | ~ l1_pre_topc(X1)
% 15.45/2.50      | ~ v2_pre_topc(X1)
% 15.45/2.50      | k2_pre_topc(X1,X0) != X0 ),
% 15.45/2.50      inference(cnf_transformation,[],[f109]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_11076,plain,
% 15.45/2.50      ( v4_pre_topc(sK4,sK3)
% 15.45/2.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 15.45/2.50      | ~ l1_pre_topc(sK3)
% 15.45/2.50      | ~ v2_pre_topc(sK3)
% 15.45/2.50      | k2_pre_topc(sK3,sK4) != sK4 ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_34]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_11077,plain,
% 15.45/2.50      ( k2_pre_topc(sK3,sK4) != sK4
% 15.45/2.50      | v4_pre_topc(sK4,sK3) = iProver_top
% 15.45/2.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.45/2.50      | l1_pre_topc(sK3) != iProver_top
% 15.45/2.50      | v2_pre_topc(sK3) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_11076]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_47,plain,
% 15.45/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_44,negated_conjecture,
% 15.45/2.50      ( v2_pre_topc(sK3) ),
% 15.45/2.50      inference(cnf_transformation,[],[f114]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_45,plain,
% 15.45/2.50      ( v2_pre_topc(sK3) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(contradiction,plain,
% 15.45/2.50      ( $false ),
% 15.45/2.50      inference(minisat,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_51534,c_41621,c_22652,c_11077,c_47,c_46,c_45]) ).
% 15.45/2.50  
% 15.45/2.50  
% 15.45/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.45/2.50  
% 15.45/2.50  ------                               Statistics
% 15.45/2.50  
% 15.45/2.50  ------ Selected
% 15.45/2.50  
% 15.45/2.50  total_time:                             1.563
% 15.45/2.50  
%------------------------------------------------------------------------------
