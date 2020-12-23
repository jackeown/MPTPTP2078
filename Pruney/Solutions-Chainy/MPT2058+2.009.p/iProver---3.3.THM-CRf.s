%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:16 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  256 (1451 expanded)
%              Number of clauses        :  159 ( 313 expanded)
%              Number of leaves         :   22 ( 405 expanded)
%              Depth                    :   34
%              Number of atoms          : 1489 (12977 expanded)
%              Number of equality atoms :  262 ( 464 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f51])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK5)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5) )
        & ( r1_waybel_7(X0,X1,sK5)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_7(X0,sK4,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2) )
            & ( r1_waybel_7(X0,sK4,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK3,X1,X2)
                | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & ( r1_waybel_7(sK3,X1,X2)
                | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r1_waybel_7(sK3,sK4,sK5)
      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & ( r1_waybel_7(sK3,sK4,sK5)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f55,f58,f57,f56])).

fof(f84,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f103,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f88,f73])).

fof(f89,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f102,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f89,f73])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f73,f73,f73,f73])).

fof(f87,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f87,f73])).

fof(f86,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f90,f73])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f73,f73,f73])).

fof(f93,plain,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f82,f73,f73,f73,f73])).

fof(f92,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f73,f73,f73])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f73,f73,f73])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4597,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4599,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5478,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4597,c_4599])).

cnf(c_12,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_664,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_665,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_70,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_667,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_32,c_31,c_30,c_70])).

cnf(c_4589,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_706,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_707,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_1184,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_707])).

cnf(c_1185,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_4617,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4589,c_1185])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_5])).

cnf(c_4590,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_4917,plain,
    ( r1_xboole_0(sK2(sK3),k2_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4617,c_4590])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_72,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_74,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_5298,plain,
    ( r1_xboole_0(sK2(sK3),k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4917,c_33,c_34,c_35,c_74])).

cnf(c_5715,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5478,c_5298])).

cnf(c_27,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_26,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_28,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_508,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_509,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_513,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_29])).

cnf(c_514,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_513])).

cnf(c_1255,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_514,c_707])).

cnf(c_1256,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1255])).

cnf(c_1260,plain,
    ( v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_32])).

cnf(c_1261,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1260])).

cnf(c_1701,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1261])).

cnf(c_1979,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1701])).

cnf(c_3103,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1979])).

cnf(c_4581,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3103])).

cnf(c_4699,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4581,c_1185])).

cnf(c_5261,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4699])).

cnf(c_5640,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5261])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_22,negated_conjecture,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_243,plain,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_631,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_632,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_32,c_30])).

cnf(c_1035,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
    | sK5 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_243,c_636])).

cnf(c_1036,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_1035])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1038,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1036,c_24])).

cnf(c_1039,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_1038])).

cnf(c_1075,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1039])).

cnf(c_1076,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1075])).

cnf(c_76,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1080,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1076,c_32,c_30,c_76])).

cnf(c_1656,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1080,c_26])).

cnf(c_1657,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1656])).

cnf(c_1661,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1657,c_29])).

cnf(c_1662,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1661])).

cnf(c_2005,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1662])).

cnf(c_3099,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2005])).

cnf(c_4174,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3099])).

cnf(c_4582,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) != iProver_top
    | r1_waybel_7(sK3,sK4,sK5) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4174])).

cnf(c_21,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_547,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_548,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK4)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_552,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_29])).

cnf(c_553,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_1173,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_553,c_707])).

cnf(c_1174,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v2_struct_0(sK3)
    | k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1176,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_32,c_27,c_26,c_25])).

cnf(c_3107,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_1176])).

cnf(c_4712,plain,
    ( r1_waybel_7(sK3,sK4,sK5) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4582,c_3107])).

cnf(c_23,negated_conjecture,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_245,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_598,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_599,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_603,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_32,c_30])).

cnf(c_1009,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
    | sK5 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_245,c_603])).

cnf(c_1010,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1012,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | r1_waybel_7(sK3,sK4,sK5)
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_24])).

cnf(c_1013,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_1012])).

cnf(c_1123,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1013])).

cnf(c_1124,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1123])).

cnf(c_1128,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_32,c_30,c_76])).

cnf(c_1611,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1128,c_26])).

cnf(c_1612,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1611])).

cnf(c_1616,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK3,sK4,sK5)
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1612,c_29])).

cnf(c_1617,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1616])).

cnf(c_2043,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1617])).

cnf(c_3095,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2043])).

cnf(c_4175,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3095])).

cnf(c_4584,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) = iProver_top
    | r1_waybel_7(sK3,sK4,sK5) = iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4175])).

cnf(c_4688,plain,
    ( r1_waybel_7(sK3,sK4,sK5) = iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4584,c_3107])).

cnf(c_4718,plain,
    ( v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4712,c_4688])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1222,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_707])).

cnf(c_1223,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_1227,plain,
    ( ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_32])).

cnf(c_1228,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1227])).

cnf(c_1551,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1228,c_26])).

cnf(c_1552,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1551])).

cnf(c_1556,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1552,c_29])).

cnf(c_1557,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1556])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1557])).

cnf(c_3087,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2104])).

cnf(c_4587,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3087])).

cnf(c_4663,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4587,c_1185])).

cnf(c_5168,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4663])).

cnf(c_5304,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5168,c_40])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4595,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4595,c_6])).

cnf(c_5311,plain,
    ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5304,c_4614])).

cnf(c_4173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3099])).

cnf(c_4583,plain,
    ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4173])).

cnf(c_4674,plain,
    ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4583,c_1185])).

cnf(c_5177,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4674])).

cnf(c_5354,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5177])).

cnf(c_5356,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5354,c_40])).

cnf(c_5363,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5356,c_4614])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1189,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_707])).

cnf(c_1190,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1189])).

cnf(c_1194,plain,
    ( v4_orders_2(k3_yellow19(sK3,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1190,c_32])).

cnf(c_1195,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1194])).

cnf(c_1581,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1195,c_26])).

cnf(c_1582,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1581])).

cnf(c_1586,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1582,c_29])).

cnf(c_1587,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1586])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1587])).

cnf(c_3091,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2081])).

cnf(c_4586,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3091])).

cnf(c_4652,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4586,c_1185])).

cnf(c_5252,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4652])).

cnf(c_5557,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5252,c_40])).

cnf(c_5564,plain,
    ( v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5557,c_4614])).

cnf(c_5642,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5640,c_40,c_4718,c_5311,c_5363,c_5564])).

cnf(c_5648,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5642,c_4614])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5715,c_5648])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.34/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.01  
% 2.34/1.01  ------  iProver source info
% 2.34/1.01  
% 2.34/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.01  git: non_committed_changes: false
% 2.34/1.01  git: last_make_outside_of_git: false
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     num_symb
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       true
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  ------ Parsing...
% 2.34/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.01  ------ Proving...
% 2.34/1.01  ------ Problem Properties 
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  clauses                                 23
% 2.34/1.01  conjectures                             4
% 2.34/1.01  EPR                                     4
% 2.34/1.01  Horn                                    16
% 2.34/1.01  unary                                   10
% 2.34/1.01  binary                                  4
% 2.34/1.01  lits                                    64
% 2.34/1.01  lits eq                                 11
% 2.34/1.01  fd_pure                                 0
% 2.34/1.01  fd_pseudo                               0
% 2.34/1.01  fd_cond                                 0
% 2.34/1.01  fd_pseudo_cond                          0
% 2.34/1.01  AC symbols                              0
% 2.34/1.01  
% 2.34/1.01  ------ Schedule dynamic 5 is on 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  Current options:
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     none
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       false
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ Proving...
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS status Theorem for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  fof(f2,axiom,(
% 2.34/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f18,plain,(
% 2.34/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.34/1.01    inference(rectify,[],[f2])).
% 2.34/1.01  
% 2.34/1.01  fof(f25,plain,(
% 2.34/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.34/1.01    inference(ennf_transformation,[],[f18])).
% 2.34/1.01  
% 2.34/1.01  fof(f49,plain,(
% 2.34/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f50,plain,(
% 2.34/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f49])).
% 2.34/1.01  
% 2.34/1.01  fof(f63,plain,(
% 2.34/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f50])).
% 2.34/1.01  
% 2.34/1.01  fof(f1,axiom,(
% 2.34/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f45,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(nnf_transformation,[],[f1])).
% 2.34/1.01  
% 2.34/1.01  fof(f46,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(rectify,[],[f45])).
% 2.34/1.01  
% 2.34/1.01  fof(f47,plain,(
% 2.34/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f48,plain,(
% 2.34/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 2.34/1.01  
% 2.34/1.01  fof(f60,plain,(
% 2.34/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f48])).
% 2.34/1.01  
% 2.34/1.01  fof(f9,axiom,(
% 2.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f24,plain,(
% 2.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.34/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.34/1.01  
% 2.34/1.01  fof(f31,plain,(
% 2.34/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f24])).
% 2.34/1.01  
% 2.34/1.01  fof(f32,plain,(
% 2.34/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f31])).
% 2.34/1.01  
% 2.34/1.01  fof(f51,plain,(
% 2.34/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f52,plain,(
% 2.34/1.01    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f51])).
% 2.34/1.01  
% 2.34/1.01  fof(f71,plain,(
% 2.34/1.01    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f52])).
% 2.34/1.01  
% 2.34/1.01  fof(f16,conjecture,(
% 2.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f17,negated_conjecture,(
% 2.34/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.34/1.01    inference(negated_conjecture,[],[f16])).
% 2.34/1.01  
% 2.34/1.01  fof(f43,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f17])).
% 2.34/1.01  
% 2.34/1.01  fof(f44,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f43])).
% 2.34/1.01  
% 2.34/1.01  fof(f54,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/1.01    inference(nnf_transformation,[],[f44])).
% 2.34/1.01  
% 2.34/1.01  fof(f55,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f54])).
% 2.34/1.01  
% 2.34/1.01  fof(f58,plain,(
% 2.34/1.01    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK5) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5)) & (r1_waybel_7(X0,X1,sK5) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f57,plain,(
% 2.34/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK4,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2)) & (r1_waybel_7(X0,sK4,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f56,plain,(
% 2.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK3,X1,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & (r1_waybel_7(sK3,X1,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f59,plain,(
% 2.34/1.01    (((~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & (r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f55,f58,f57,f56])).
% 2.34/1.01  
% 2.34/1.01  fof(f84,plain,(
% 2.34/1.01    v2_pre_topc(sK3)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f83,plain,(
% 2.34/1.01    ~v2_struct_0(sK3)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f85,plain,(
% 2.34/1.01    l1_pre_topc(sK3)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f7,axiom,(
% 2.34/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f29,plain,(
% 2.34/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f7])).
% 2.34/1.01  
% 2.34/1.01  fof(f69,plain,(
% 2.34/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f29])).
% 2.34/1.01  
% 2.34/1.01  fof(f8,axiom,(
% 2.34/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f30,plain,(
% 2.34/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f8])).
% 2.34/1.01  
% 2.34/1.01  fof(f70,plain,(
% 2.34/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f30])).
% 2.34/1.01  
% 2.34/1.01  fof(f6,axiom,(
% 2.34/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f19,plain,(
% 2.34/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.34/1.01    inference(unused_predicate_definition_removal,[],[f6])).
% 2.34/1.01  
% 2.34/1.01  fof(f28,plain,(
% 2.34/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.34/1.01    inference(ennf_transformation,[],[f19])).
% 2.34/1.01  
% 2.34/1.01  fof(f68,plain,(
% 2.34/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f28])).
% 2.34/1.01  
% 2.34/1.01  fof(f3,axiom,(
% 2.34/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f26,plain,(
% 2.34/1.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.34/1.01    inference(ennf_transformation,[],[f3])).
% 2.34/1.01  
% 2.34/1.01  fof(f27,plain,(
% 2.34/1.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.34/1.01    inference(flattening,[],[f26])).
% 2.34/1.01  
% 2.34/1.01  fof(f65,plain,(
% 2.34/1.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f27])).
% 2.34/1.01  
% 2.34/1.01  fof(f72,plain,(
% 2.34/1.01    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f52])).
% 2.34/1.01  
% 2.34/1.01  fof(f88,plain,(
% 2.34/1.01    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f10,axiom,(
% 2.34/1.01    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f73,plain,(
% 2.34/1.01    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f10])).
% 2.34/1.01  
% 2.34/1.01  fof(f103,plain,(
% 2.34/1.01    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.34/1.01    inference(definition_unfolding,[],[f88,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f89,plain,(
% 2.34/1.01    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f102,plain,(
% 2.34/1.01    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.34/1.01    inference(definition_unfolding,[],[f89,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f13,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f21,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    inference(pure_predicate_removal,[],[f13])).
% 2.34/1.01  
% 2.34/1.01  fof(f37,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f21])).
% 2.34/1.01  
% 2.34/1.01  fof(f38,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f37])).
% 2.34/1.01  
% 2.34/1.01  fof(f79,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f38])).
% 2.34/1.01  
% 2.34/1.01  fof(f98,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(definition_unfolding,[],[f79,f73,f73,f73,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f87,plain,(
% 2.34/1.01    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f104,plain,(
% 2.34/1.01    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.34/1.01    inference(definition_unfolding,[],[f87,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f86,plain,(
% 2.34/1.01    ~v1_xboole_0(sK4)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f90,plain,(
% 2.34/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f101,plain,(
% 2.34/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 2.34/1.01    inference(definition_unfolding,[],[f90,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f11,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f22,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    inference(pure_predicate_removal,[],[f11])).
% 2.34/1.01  
% 2.34/1.01  fof(f33,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f22])).
% 2.34/1.01  
% 2.34/1.01  fof(f34,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f33])).
% 2.34/1.01  
% 2.34/1.01  fof(f75,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f34])).
% 2.34/1.01  
% 2.34/1.01  fof(f94,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(definition_unfolding,[],[f75,f73,f73,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f93,plain,(
% 2.34/1.01    ~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f14,axiom,(
% 2.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f39,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f14])).
% 2.34/1.01  
% 2.34/1.01  fof(f40,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f39])).
% 2.34/1.01  
% 2.34/1.01  fof(f53,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(nnf_transformation,[],[f40])).
% 2.34/1.01  
% 2.34/1.01  fof(f81,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f53])).
% 2.34/1.01  
% 2.34/1.01  fof(f91,plain,(
% 2.34/1.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f15,axiom,(
% 2.34/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f41,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f15])).
% 2.34/1.01  
% 2.34/1.01  fof(f42,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f41])).
% 2.34/1.01  
% 2.34/1.01  fof(f82,plain,(
% 2.34/1.01    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f42])).
% 2.34/1.01  
% 2.34/1.01  fof(f100,plain,(
% 2.34/1.01    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(definition_unfolding,[],[f82,f73,f73,f73,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f92,plain,(
% 2.34/1.01    r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)),
% 2.34/1.01    inference(cnf_transformation,[],[f59])).
% 2.34/1.01  
% 2.34/1.01  fof(f80,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f53])).
% 2.34/1.01  
% 2.34/1.01  fof(f74,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f34])).
% 2.34/1.01  
% 2.34/1.01  fof(f95,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(definition_unfolding,[],[f74,f73,f73,f73])).
% 2.34/1.01  
% 2.34/1.01  fof(f5,axiom,(
% 2.34/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f67,plain,(
% 2.34/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f5])).
% 2.34/1.01  
% 2.34/1.01  fof(f4,axiom,(
% 2.34/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f66,plain,(
% 2.34/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.34/1.01    inference(cnf_transformation,[],[f4])).
% 2.34/1.01  
% 2.34/1.01  fof(f12,axiom,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f20,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    inference(pure_predicate_removal,[],[f12])).
% 2.34/1.01  
% 2.34/1.01  fof(f23,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.34/1.01    inference(pure_predicate_removal,[],[f20])).
% 2.34/1.01  
% 2.34/1.01  fof(f35,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f36,plain,(
% 2.34/1.01    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.01    inference(flattening,[],[f35])).
% 2.34/1.01  
% 2.34/1.01  fof(f77,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f36])).
% 2.34/1.01  
% 2.34/1.01  fof(f96,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.01    inference(definition_unfolding,[],[f77,f73,f73,f73])).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3,plain,
% 2.34/1.01      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4597,plain,
% 2.34/1.01      ( r1_xboole_0(X0,X1) = iProver_top
% 2.34/1.01      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1,plain,
% 2.34/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4599,plain,
% 2.34/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.34/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5478,plain,
% 2.34/1.01      ( r1_xboole_0(X0,X1) = iProver_top
% 2.34/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_4597,c_4599]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_12,plain,
% 2.34/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | ~ v2_pre_topc(X0)
% 2.34/1.01      | ~ l1_pre_topc(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_31,negated_conjecture,
% 2.34/1.01      ( v2_pre_topc(sK3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_664,plain,
% 2.34/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | ~ l1_pre_topc(X0)
% 2.34/1.01      | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_665,plain,
% 2.34/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ l1_pre_topc(sK3) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_664]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_32,negated_conjecture,
% 2.34/1.01      ( ~ v2_struct_0(sK3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_30,negated_conjecture,
% 2.34/1.01      ( l1_pre_topc(sK3) ),
% 2.34/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_70,plain,
% 2.34/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ v2_pre_topc(sK3)
% 2.34/1.01      | ~ l1_pre_topc(sK3) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_667,plain,
% 2.34/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_665,c_32,c_31,c_30,c_70]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4589,plain,
% 2.34/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_9,plain,
% 2.34/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_10,plain,
% 2.34/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_706,plain,
% 2.34/1.01      ( l1_struct_0(X0) | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_707,plain,
% 2.34/1.01      ( l1_struct_0(sK3) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_706]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1184,plain,
% 2.34/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_707]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1185,plain,
% 2.34/1.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1184]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4617,plain,
% 2.34/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4589,c_1185]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_8,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5,plain,
% 2.34/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_426,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/1.01      | ~ r1_xboole_0(X0,X1)
% 2.34/1.01      | v1_xboole_0(X0) ),
% 2.34/1.01      inference(resolution,[status(thm)],[c_8,c_5]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4590,plain,
% 2.34/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.34/1.01      | r1_xboole_0(X0,X1) != iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4917,plain,
% 2.34/1.01      ( r1_xboole_0(sK2(sK3),k2_struct_0(sK3)) != iProver_top
% 2.34/1.01      | v1_xboole_0(sK2(sK3)) = iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_4617,c_4590]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_33,plain,
% 2.34/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_34,plain,
% 2.34/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_35,plain,
% 2.34/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_11,plain,
% 2.34/1.01      ( v2_struct_0(X0)
% 2.34/1.01      | ~ v2_pre_topc(X0)
% 2.34/1.01      | ~ l1_pre_topc(X0)
% 2.34/1.01      | ~ v1_xboole_0(sK2(X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_72,plain,
% 2.34/1.01      ( v2_struct_0(X0) = iProver_top
% 2.34/1.01      | v2_pre_topc(X0) != iProver_top
% 2.34/1.01      | l1_pre_topc(X0) != iProver_top
% 2.34/1.01      | v1_xboole_0(sK2(X0)) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_74,plain,
% 2.34/1.01      ( v2_struct_0(sK3) = iProver_top
% 2.34/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.34/1.01      | l1_pre_topc(sK3) != iProver_top
% 2.34/1.01      | v1_xboole_0(sK2(sK3)) != iProver_top ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_72]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5298,plain,
% 2.34/1.01      ( r1_xboole_0(sK2(sK3),k2_struct_0(sK3)) != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_4917,c_33,c_34,c_35,c_74]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5715,plain,
% 2.34/1.01      ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_5478,c_5298]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_27,negated_conjecture,
% 2.34/1.01      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f103]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_26,negated_conjecture,
% 2.34/1.01      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_17,plain,
% 2.34/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_28,negated_conjecture,
% 2.34/1.01      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f104]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_508,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_509,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_508]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_29,negated_conjecture,
% 2.34/1.01      ( ~ v1_xboole_0(sK4) ),
% 2.34/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_513,plain,
% 2.34/1.01      ( v1_xboole_0(X0)
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_509,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_514,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_513]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1255,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | sK3 != X1 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_514,c_707]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1256,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1255]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1260,plain,
% 2.34/1.01      ( v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1256,c_32]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1261,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1260]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1701,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_1261]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1979,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1701]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3103,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_1979]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4581,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3103]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4699,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4581,c_1185]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5261,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.34/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(equality_resolution,[status(thm)],[c_4699]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5640,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_5261]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_25,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 2.34/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_40,plain,
% 2.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_13,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_22,negated_conjecture,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.34/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_243,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.34/1.01      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_19,plain,
% 2.34/1.01      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.34/1.01      | r3_waybel_9(X0,X1,X2)
% 2.34/1.01      | ~ l1_waybel_0(X1,X0)
% 2.34/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.01      | ~ v7_waybel_0(X1)
% 2.34/1.01      | ~ v4_orders_2(X1)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ v2_pre_topc(X0)
% 2.34/1.01      | ~ l1_pre_topc(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_631,plain,
% 2.34/1.01      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.34/1.01      | r3_waybel_9(X0,X1,X2)
% 2.34/1.01      | ~ l1_waybel_0(X1,X0)
% 2.34/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.01      | ~ v7_waybel_0(X1)
% 2.34/1.01      | ~ v4_orders_2(X1)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_pre_topc(X0)
% 2.34/1.01      | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_632,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | r3_waybel_9(sK3,X0,X1)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ l1_pre_topc(sK3) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_636,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | r3_waybel_9(sK3,X0,X1)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_632,c_32,c_30]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1035,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
% 2.34/1.01      | sK5 != X1
% 2.34/1.01      | sK3 != sK3 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_243,c_636]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1036,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1035]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_24,negated_conjecture,
% 2.34/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1038,plain,
% 2.34/1.01      ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1036,c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1039,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1038]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1075,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
% 2.34/1.01      | sK3 != X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_1039]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1076,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ l1_struct_0(sK3)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1075]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_76,plain,
% 2.34/1.01      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1080,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1076,c_32,c_30,c_76]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1656,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_1080,c_26]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1657,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1656]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1661,plain,
% 2.34/1.01      ( v1_xboole_0(X0)
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1657,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1662,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1661]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2005,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1662]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3099,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_2005]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4174,plain,
% 2.34/1.01      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | sP0_iProver_split ),
% 2.34/1.01      inference(splitting,
% 2.34/1.01                [splitting(split),new_symbols(definition,[])],
% 2.34/1.01                [c_3099]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4582,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) != iProver_top
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | sP0_iProver_split = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_4174]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_21,plain,
% 2.34/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_547,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_struct_0(X1)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_548,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | ~ l1_struct_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_547]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_552,plain,
% 2.34/1.01      ( ~ l1_struct_0(X0)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_548,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_553,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | ~ l1_struct_0(X0)
% 2.34/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_552]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1173,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.34/1.01      | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_553,c_707]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1174,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.34/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1173]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1176,plain,
% 2.34/1.01      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
% 2.34/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1174,c_32,c_27,c_26,c_25]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3107,plain,
% 2.34/1.01      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4 ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_1176]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4712,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,sK4,sK5) != iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | sP0_iProver_split = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4582,c_3107]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_23,negated_conjecture,
% 2.34/1.01      ( r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.34/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_245,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.34/1.01      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_20,plain,
% 2.34/1.01      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.34/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.34/1.01      | ~ l1_waybel_0(X1,X0)
% 2.34/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.01      | ~ v7_waybel_0(X1)
% 2.34/1.01      | ~ v4_orders_2(X1)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ v2_pre_topc(X0)
% 2.34/1.01      | ~ l1_pre_topc(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_598,plain,
% 2.34/1.01      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.34/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.34/1.01      | ~ l1_waybel_0(X1,X0)
% 2.34/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.01      | ~ v7_waybel_0(X1)
% 2.34/1.01      | ~ v4_orders_2(X1)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(X1)
% 2.34/1.01      | ~ l1_pre_topc(X0)
% 2.34/1.01      | sK3 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_599,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | ~ r3_waybel_9(sK3,X0,X1)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ l1_pre_topc(sK3) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_598]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_603,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | ~ r3_waybel_9(sK3,X0,X1)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_599,c_32,c_30]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1009,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(X0,sK3)
% 2.34/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(X0)
% 2.34/1.01      | ~ v4_orders_2(X0)
% 2.34/1.01      | v2_struct_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
% 2.34/1.01      | sK5 != X1
% 2.34/1.01      | sK3 != sK3 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_245,c_603]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1010,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1009]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1012,plain,
% 2.34/1.01      ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1010,c_24]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1013,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1012]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1123,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
% 2.34/1.01      | sK3 != X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_1013]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1124,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | ~ l1_struct_0(sK3)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1123]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1128,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1124,c_32,c_30,c_76]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1611,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_1128,c_26]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1612,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1611]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1616,plain,
% 2.34/1.01      ( v1_xboole_0(X0)
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1612,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1617,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1616]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2043,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1617]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3095,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_2043]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4175,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5)
% 2.34/1.01      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.34/1.01      | sP0_iProver_split ),
% 2.34/1.01      inference(splitting,
% 2.34/1.01                [splitting(split),new_symbols(definition,[])],
% 2.34/1.01                [c_3095]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4584,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) = iProver_top
% 2.34/1.01      | r1_waybel_7(sK3,sK4,sK5) = iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | sP0_iProver_split = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_4175]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4688,plain,
% 2.34/1.01      ( r1_waybel_7(sK3,sK4,sK5) = iProver_top
% 2.34/1.01      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | sP0_iProver_split = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4584,c_3107]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4718,plain,
% 2.34/1.01      ( v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | sP0_iProver_split = iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_4712,c_4688]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_14,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1222,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | sK3 != X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_707]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1223,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1222]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1227,plain,
% 2.34/1.01      ( ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1223,c_32]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1228,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1227]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1551,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_1228,c_26]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1552,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1551]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1556,plain,
% 2.34/1.01      ( v1_xboole_0(X0)
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1552,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1557,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1556]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2104,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1557]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3087,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_2104]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4587,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3087]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4663,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4587,c_1185]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5168,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(equality_resolution,[status(thm)],[c_4663]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5304,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5168,c_40]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_7,plain,
% 2.34/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4595,plain,
% 2.34/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_6,plain,
% 2.34/1.01      ( k2_subset_1(X0) = X0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4614,plain,
% 2.34/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4595,c_6]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5311,plain,
% 2.34/1.01      ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5304,c_4614]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4173,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | ~ sP0_iProver_split ),
% 2.34/1.01      inference(splitting,
% 2.34/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.34/1.01                [c_3099]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4583,plain,
% 2.34/1.01      ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_4173]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4674,plain,
% 2.34/1.01      ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4583,c_1185]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5177,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.34/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(equality_resolution,[status(thm)],[c_4674]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5354,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_5177]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5356,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5354,c_40]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5363,plain,
% 2.34/1.01      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.34/1.01      | sP0_iProver_split != iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5356,c_4614]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_15,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | ~ l1_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1189,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.34/1.01      | v2_struct_0(X2)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | sK3 != X2 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_707]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1190,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v2_struct_0(sK3)
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1189]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1194,plain,
% 2.34/1.01      ( v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1190,c_32]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1195,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1194]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1581,plain,
% 2.34/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(X1)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.34/1.01      | sK4 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_1195,c_26]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1582,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | v1_xboole_0(sK4)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_1581]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1586,plain,
% 2.34/1.01      ( v1_xboole_0(X0)
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1582,c_29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1587,plain,
% 2.34/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_1586]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2081,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | sK4 != sK4 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1587]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3091,plain,
% 2.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.34/1.01      | v1_xboole_0(X0)
% 2.34/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.34/1.01      inference(equality_resolution_simp,[status(thm)],[c_2081]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4586,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3091]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4652,plain,
% 2.34/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_4586,c_1185]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5252,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(equality_resolution,[status(thm)],[c_4652]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5557,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5252,c_40]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5564,plain,
% 2.34/1.01      ( v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5557,c_4614]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5642,plain,
% 2.34/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.34/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5640,c_40,c_4718,c_5311,c_5363,c_5564]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5648,plain,
% 2.34/1.01      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_5642,c_4614]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(contradiction,plain,
% 2.34/1.01      ( $false ),
% 2.34/1.01      inference(minisat,[status(thm)],[c_5715,c_5648]) ).
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  ------                               Statistics
% 2.34/1.01  
% 2.34/1.01  ------ General
% 2.34/1.01  
% 2.34/1.01  abstr_ref_over_cycles:                  0
% 2.34/1.01  abstr_ref_under_cycles:                 0
% 2.34/1.01  gc_basic_clause_elim:                   0
% 2.34/1.01  forced_gc_time:                         0
% 2.34/1.01  parsing_time:                           0.015
% 2.34/1.01  unif_index_cands_time:                  0.
% 2.34/1.01  unif_index_add_time:                    0.
% 2.34/1.01  orderings_time:                         0.
% 2.34/1.01  out_proof_time:                         0.016
% 2.34/1.01  total_time:                             0.237
% 2.34/1.01  num_of_symbols:                         63
% 2.34/1.01  num_of_terms:                           2287
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing
% 2.34/1.01  
% 2.34/1.01  num_of_splits:                          2
% 2.34/1.01  num_of_split_atoms:                     1
% 2.34/1.01  num_of_reused_defs:                     1
% 2.34/1.01  num_eq_ax_congr_red:                    27
% 2.34/1.01  num_of_sem_filtered_clauses:            1
% 2.34/1.01  num_of_subtypes:                        0
% 2.34/1.01  monotx_restored_types:                  0
% 2.34/1.01  sat_num_of_epr_types:                   0
% 2.34/1.01  sat_num_of_non_cyclic_types:            0
% 2.34/1.01  sat_guarded_non_collapsed_types:        0
% 2.34/1.01  num_pure_diseq_elim:                    0
% 2.34/1.01  simp_replaced_by:                       0
% 2.34/1.01  res_preprocessed:                       131
% 2.34/1.01  prep_upred:                             0
% 2.34/1.01  prep_unflattend:                        72
% 2.34/1.01  smt_new_axioms:                         0
% 2.34/1.01  pred_elim_cands:                        8
% 2.34/1.01  pred_elim:                              9
% 2.34/1.01  pred_elim_cl:                           10
% 2.34/1.01  pred_elim_cycles:                       26
% 2.34/1.01  merged_defs:                            2
% 2.34/1.01  merged_defs_ncl:                        0
% 2.34/1.01  bin_hyper_res:                          2
% 2.34/1.01  prep_cycles:                            4
% 2.34/1.01  pred_elim_time:                         0.131
% 2.34/1.01  splitting_time:                         0.
% 2.34/1.01  sem_filter_time:                        0.
% 2.34/1.01  monotx_time:                            0.
% 2.34/1.01  subtype_inf_time:                       0.
% 2.34/1.01  
% 2.34/1.01  ------ Problem properties
% 2.34/1.01  
% 2.34/1.01  clauses:                                23
% 2.34/1.01  conjectures:                            4
% 2.34/1.01  epr:                                    4
% 2.34/1.01  horn:                                   16
% 2.34/1.01  ground:                                 10
% 2.34/1.01  unary:                                  10
% 2.34/1.01  binary:                                 4
% 2.34/1.01  lits:                                   64
% 2.34/1.01  lits_eq:                                11
% 2.34/1.01  fd_pure:                                0
% 2.34/1.01  fd_pseudo:                              0
% 2.34/1.01  fd_cond:                                0
% 2.34/1.01  fd_pseudo_cond:                         0
% 2.34/1.01  ac_symbols:                             0
% 2.34/1.01  
% 2.34/1.01  ------ Propositional Solver
% 2.34/1.01  
% 2.34/1.01  prop_solver_calls:                      26
% 2.34/1.01  prop_fast_solver_calls:                 1981
% 2.34/1.01  smt_solver_calls:                       0
% 2.34/1.01  smt_fast_solver_calls:                  0
% 2.34/1.01  prop_num_of_clauses:                    1014
% 2.34/1.01  prop_preprocess_simplified:             4350
% 2.34/1.01  prop_fo_subsumed:                       49
% 2.34/1.01  prop_solver_time:                       0.
% 2.34/1.01  smt_solver_time:                        0.
% 2.34/1.01  smt_fast_solver_time:                   0.
% 2.34/1.01  prop_fast_solver_time:                  0.
% 2.34/1.01  prop_unsat_core_time:                   0.
% 2.34/1.01  
% 2.34/1.01  ------ QBF
% 2.34/1.01  
% 2.34/1.01  qbf_q_res:                              0
% 2.34/1.01  qbf_num_tautologies:                    0
% 2.34/1.01  qbf_prep_cycles:                        0
% 2.34/1.01  
% 2.34/1.01  ------ BMC1
% 2.34/1.01  
% 2.34/1.01  bmc1_current_bound:                     -1
% 2.34/1.01  bmc1_last_solved_bound:                 -1
% 2.34/1.01  bmc1_unsat_core_size:                   -1
% 2.34/1.01  bmc1_unsat_core_parents_size:           -1
% 2.34/1.01  bmc1_merge_next_fun:                    0
% 2.34/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation
% 2.34/1.01  
% 2.34/1.01  inst_num_of_clauses:                    212
% 2.34/1.01  inst_num_in_passive:                    24
% 2.34/1.01  inst_num_in_active:                     144
% 2.34/1.01  inst_num_in_unprocessed:                44
% 2.34/1.01  inst_num_of_loops:                      150
% 2.34/1.01  inst_num_of_learning_restarts:          0
% 2.34/1.01  inst_num_moves_active_passive:          4
% 2.34/1.01  inst_lit_activity:                      0
% 2.34/1.01  inst_lit_activity_moves:                0
% 2.34/1.01  inst_num_tautologies:                   0
% 2.34/1.01  inst_num_prop_implied:                  0
% 2.34/1.01  inst_num_existing_simplified:           0
% 2.34/1.01  inst_num_eq_res_simplified:             0
% 2.34/1.01  inst_num_child_elim:                    0
% 2.34/1.01  inst_num_of_dismatching_blockings:      51
% 2.34/1.01  inst_num_of_non_proper_insts:           166
% 2.34/1.01  inst_num_of_duplicates:                 0
% 2.34/1.01  inst_inst_num_from_inst_to_res:         0
% 2.34/1.01  inst_dismatching_checking_time:         0.
% 2.34/1.01  
% 2.34/1.01  ------ Resolution
% 2.34/1.01  
% 2.34/1.01  res_num_of_clauses:                     0
% 2.34/1.01  res_num_in_passive:                     0
% 2.34/1.01  res_num_in_active:                      0
% 2.34/1.01  res_num_of_loops:                       135
% 2.34/1.01  res_forward_subset_subsumed:            23
% 2.34/1.01  res_backward_subset_subsumed:           0
% 2.34/1.01  res_forward_subsumed:                   0
% 2.34/1.01  res_backward_subsumed:                  0
% 2.34/1.01  res_forward_subsumption_resolution:     2
% 2.34/1.01  res_backward_subsumption_resolution:    0
% 2.34/1.01  res_clause_to_clause_subsumption:       278
% 2.34/1.01  res_orphan_elimination:                 0
% 2.34/1.01  res_tautology_del:                      22
% 2.34/1.01  res_num_eq_res_simplified:              6
% 2.34/1.01  res_num_sel_changes:                    0
% 2.34/1.01  res_moves_from_active_to_pass:          0
% 2.34/1.01  
% 2.34/1.01  ------ Superposition
% 2.34/1.01  
% 2.34/1.01  sup_time_total:                         0.
% 2.34/1.01  sup_time_generating:                    0.
% 2.34/1.01  sup_time_sim_full:                      0.
% 2.34/1.01  sup_time_sim_immed:                     0.
% 2.34/1.01  
% 2.34/1.01  sup_num_of_clauses:                     31
% 2.34/1.01  sup_num_in_active:                      29
% 2.34/1.01  sup_num_in_passive:                     2
% 2.34/1.01  sup_num_of_loops:                       29
% 2.34/1.01  sup_fw_superposition:                   3
% 2.34/1.01  sup_bw_superposition:                   11
% 2.34/1.01  sup_immediate_simplified:               1
% 2.34/1.01  sup_given_eliminated:                   0
% 2.34/1.01  comparisons_done:                       0
% 2.34/1.01  comparisons_avoided:                    0
% 2.34/1.01  
% 2.34/1.01  ------ Simplifications
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  sim_fw_subset_subsumed:                 0
% 2.34/1.01  sim_bw_subset_subsumed:                 1
% 2.34/1.01  sim_fw_subsumed:                        1
% 2.34/1.01  sim_bw_subsumed:                        1
% 2.34/1.01  sim_fw_subsumption_res:                 5
% 2.34/1.01  sim_bw_subsumption_res:                 0
% 2.34/1.01  sim_tautology_del:                      1
% 2.34/1.01  sim_eq_tautology_del:                   0
% 2.34/1.01  sim_eq_res_simp:                        2
% 2.34/1.01  sim_fw_demodulated:                     0
% 2.34/1.01  sim_bw_demodulated:                     0
% 2.34/1.01  sim_light_normalised:                   10
% 2.34/1.01  sim_joinable_taut:                      0
% 2.34/1.01  sim_joinable_simp:                      0
% 2.34/1.01  sim_ac_normalised:                      0
% 2.34/1.01  sim_smt_subsumption:                    0
% 2.34/1.01  
%------------------------------------------------------------------------------
