%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:56 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 478 expanded)
%              Number of clauses        :   77 ( 102 expanded)
%              Number of leaves         :   20 ( 166 expanded)
%              Depth                    :   17
%              Number of atoms          :  823 (3505 expanded)
%              Number of equality atoms :  107 ( 109 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f49])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK4,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK4),X3)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & r1_xboole_0(u1_struct_0(sK4),X1)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(X0,sK3),k2_tmap_1(X0,k6_tmap_1(X0,sK3),k7_tmap_1(X0,sK3),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK3)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK2,X1),k2_tmap_1(sK2,k6_tmap_1(sK2,X1),k7_tmap_1(sK2,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & r1_xboole_0(u1_struct_0(sK4),sK3)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f54,f53,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    r1_xboole_0(u1_struct_0(sK4),sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f84,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ~ r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3915,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v1_xboole_0(sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3194,plain,
    ( ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(sK1(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1500,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1511,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1999,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1511])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_337,plain,
    ( k4_xboole_0(X0,X1) = X0
    | u1_struct_0(sK4) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_338,plain,
    ( k4_xboole_0(u1_struct_0(sK4),sK3) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1514,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1991,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_338,c_1514])).

cnf(c_2789,plain,
    ( r2_hidden(sK5,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1999,c_1991])).

cnf(c_2790,plain,
    ( ~ r2_hidden(sK5,sK3)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2789])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2585,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k6_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1502,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_510,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_511,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_515,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_31,c_30,c_29,c_27])).

cnf(c_516,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_471,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_31,c_29,c_27])).

cnf(c_476,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_531,plain,
    ( ~ r1_tmap_1(sK2,X0,X1,X2)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_516,c_476])).

cnf(c_1491,plain,
    ( r1_tmap_1(sK2,X0,X1,X2) != iProver_top
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1501,plain,
    ( r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1884,plain,
    ( r1_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK5) != iProver_top
    | v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1501])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | l1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1790,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1798,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1805,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1806,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1831,plain,
    ( m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1832,plain,
    ( m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1831])).

cnf(c_17,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1839,plain,
    ( v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1840,plain,
    ( v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1839])).

cnf(c_2438,plain,
    ( r1_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK5) != iProver_top
    | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1884,c_32,c_33,c_34,c_35,c_39,c_1790,c_1798,c_1806,c_1832,c_1840])).

cnf(c_2539,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK5,sK3) = iProver_top
    | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_2438])).

cnf(c_2540,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,sK3)
    | v2_struct_0(k6_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2539])).

cnf(c_13,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1983,plain,
    ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1766,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_499,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_500,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_488,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_489,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3915,c_3194,c_2790,c_2585,c_2540,c_1983,c_1766,c_500,c_489,c_24,c_27,c_28,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.15/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/0.99  
% 2.15/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/0.99  
% 2.15/0.99  ------  iProver source info
% 2.15/0.99  
% 2.15/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.15/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/0.99  git: non_committed_changes: false
% 2.15/0.99  git: last_make_outside_of_git: false
% 2.15/0.99  
% 2.15/0.99  ------ 
% 2.15/0.99  
% 2.15/0.99  ------ Input Options
% 2.15/0.99  
% 2.15/0.99  --out_options                           all
% 2.15/0.99  --tptp_safe_out                         true
% 2.15/0.99  --problem_path                          ""
% 2.15/0.99  --include_path                          ""
% 2.15/0.99  --clausifier                            res/vclausify_rel
% 2.15/0.99  --clausifier_options                    --mode clausify
% 2.15/0.99  --stdin                                 false
% 2.15/0.99  --stats_out                             all
% 2.15/0.99  
% 2.15/0.99  ------ General Options
% 2.15/0.99  
% 2.15/0.99  --fof                                   false
% 2.15/0.99  --time_out_real                         305.
% 2.15/0.99  --time_out_virtual                      -1.
% 2.15/0.99  --symbol_type_check                     false
% 2.15/0.99  --clausify_out                          false
% 2.15/0.99  --sig_cnt_out                           false
% 2.15/0.99  --trig_cnt_out                          false
% 2.15/0.99  --trig_cnt_out_tolerance                1.
% 2.15/0.99  --trig_cnt_out_sk_spl                   false
% 2.15/0.99  --abstr_cl_out                          false
% 2.15/0.99  
% 2.15/0.99  ------ Global Options
% 2.15/0.99  
% 2.15/0.99  --schedule                              default
% 2.15/0.99  --add_important_lit                     false
% 2.15/0.99  --prop_solver_per_cl                    1000
% 2.15/0.99  --min_unsat_core                        false
% 2.15/0.99  --soft_assumptions                      false
% 2.15/0.99  --soft_lemma_size                       3
% 2.15/0.99  --prop_impl_unit_size                   0
% 2.15/0.99  --prop_impl_unit                        []
% 2.15/0.99  --share_sel_clauses                     true
% 2.15/0.99  --reset_solvers                         false
% 2.15/0.99  --bc_imp_inh                            [conj_cone]
% 2.15/0.99  --conj_cone_tolerance                   3.
% 2.15/0.99  --extra_neg_conj                        none
% 2.15/0.99  --large_theory_mode                     true
% 2.15/0.99  --prolific_symb_bound                   200
% 2.15/0.99  --lt_threshold                          2000
% 2.15/0.99  --clause_weak_htbl                      true
% 2.15/0.99  --gc_record_bc_elim                     false
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing Options
% 2.15/0.99  
% 2.15/0.99  --preprocessing_flag                    true
% 2.15/0.99  --time_out_prep_mult                    0.1
% 2.15/0.99  --splitting_mode                        input
% 2.15/0.99  --splitting_grd                         true
% 2.15/0.99  --splitting_cvd                         false
% 2.15/0.99  --splitting_cvd_svl                     false
% 2.15/0.99  --splitting_nvd                         32
% 2.15/0.99  --sub_typing                            true
% 2.15/0.99  --prep_gs_sim                           true
% 2.15/0.99  --prep_unflatten                        true
% 2.15/0.99  --prep_res_sim                          true
% 2.15/0.99  --prep_upred                            true
% 2.15/0.99  --prep_sem_filter                       exhaustive
% 2.15/0.99  --prep_sem_filter_out                   false
% 2.15/0.99  --pred_elim                             true
% 2.15/0.99  --res_sim_input                         true
% 2.15/0.99  --eq_ax_congr_red                       true
% 2.15/0.99  --pure_diseq_elim                       true
% 2.15/0.99  --brand_transform                       false
% 2.15/0.99  --non_eq_to_eq                          false
% 2.15/0.99  --prep_def_merge                        true
% 2.15/0.99  --prep_def_merge_prop_impl              false
% 2.15/0.99  --prep_def_merge_mbd                    true
% 2.15/0.99  --prep_def_merge_tr_red                 false
% 2.15/0.99  --prep_def_merge_tr_cl                  false
% 2.15/0.99  --smt_preprocessing                     true
% 2.15/0.99  --smt_ac_axioms                         fast
% 2.15/0.99  --preprocessed_out                      false
% 2.15/0.99  --preprocessed_stats                    false
% 2.15/0.99  
% 2.15/0.99  ------ Abstraction refinement Options
% 2.15/0.99  
% 2.15/0.99  --abstr_ref                             []
% 2.15/0.99  --abstr_ref_prep                        false
% 2.15/0.99  --abstr_ref_until_sat                   false
% 2.15/0.99  --abstr_ref_sig_restrict                funpre
% 2.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.99  --abstr_ref_under                       []
% 2.15/0.99  
% 2.15/0.99  ------ SAT Options
% 2.15/0.99  
% 2.15/0.99  --sat_mode                              false
% 2.15/0.99  --sat_fm_restart_options                ""
% 2.15/0.99  --sat_gr_def                            false
% 2.15/0.99  --sat_epr_types                         true
% 2.15/0.99  --sat_non_cyclic_types                  false
% 2.15/0.99  --sat_finite_models                     false
% 2.15/0.99  --sat_fm_lemmas                         false
% 2.15/0.99  --sat_fm_prep                           false
% 2.15/0.99  --sat_fm_uc_incr                        true
% 2.15/0.99  --sat_out_model                         small
% 2.15/0.99  --sat_out_clauses                       false
% 2.15/0.99  
% 2.15/0.99  ------ QBF Options
% 2.15/0.99  
% 2.15/0.99  --qbf_mode                              false
% 2.15/0.99  --qbf_elim_univ                         false
% 2.15/0.99  --qbf_dom_inst                          none
% 2.15/0.99  --qbf_dom_pre_inst                      false
% 2.15/0.99  --qbf_sk_in                             false
% 2.15/0.99  --qbf_pred_elim                         true
% 2.15/0.99  --qbf_split                             512
% 2.15/0.99  
% 2.15/0.99  ------ BMC1 Options
% 2.15/0.99  
% 2.15/0.99  --bmc1_incremental                      false
% 2.15/0.99  --bmc1_axioms                           reachable_all
% 2.15/0.99  --bmc1_min_bound                        0
% 2.15/0.99  --bmc1_max_bound                        -1
% 2.15/0.99  --bmc1_max_bound_default                -1
% 2.15/0.99  --bmc1_symbol_reachability              true
% 2.15/0.99  --bmc1_property_lemmas                  false
% 2.15/0.99  --bmc1_k_induction                      false
% 2.15/0.99  --bmc1_non_equiv_states                 false
% 2.15/0.99  --bmc1_deadlock                         false
% 2.15/0.99  --bmc1_ucm                              false
% 2.15/0.99  --bmc1_add_unsat_core                   none
% 2.15/0.99  --bmc1_unsat_core_children              false
% 2.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/0.99  --bmc1_out_stat                         full
% 2.15/0.99  --bmc1_ground_init                      false
% 2.15/0.99  --bmc1_pre_inst_next_state              false
% 2.15/0.99  --bmc1_pre_inst_state                   false
% 2.15/0.99  --bmc1_pre_inst_reach_state             false
% 2.15/0.99  --bmc1_out_unsat_core                   false
% 2.15/0.99  --bmc1_aig_witness_out                  false
% 2.15/0.99  --bmc1_verbose                          false
% 2.15/0.99  --bmc1_dump_clauses_tptp                false
% 2.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.15/0.99  --bmc1_dump_file                        -
% 2.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.15/0.99  --bmc1_ucm_extend_mode                  1
% 2.15/0.99  --bmc1_ucm_init_mode                    2
% 2.15/0.99  --bmc1_ucm_cone_mode                    none
% 2.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.15/0.99  --bmc1_ucm_relax_model                  4
% 2.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/0.99  --bmc1_ucm_layered_model                none
% 2.15/0.99  --bmc1_ucm_max_lemma_size               10
% 2.15/0.99  
% 2.15/0.99  ------ AIG Options
% 2.15/0.99  
% 2.15/0.99  --aig_mode                              false
% 2.15/0.99  
% 2.15/0.99  ------ Instantiation Options
% 2.15/0.99  
% 2.15/0.99  --instantiation_flag                    true
% 2.15/0.99  --inst_sos_flag                         false
% 2.15/0.99  --inst_sos_phase                        true
% 2.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel_side                     num_symb
% 2.15/0.99  --inst_solver_per_active                1400
% 2.15/0.99  --inst_solver_calls_frac                1.
% 2.15/0.99  --inst_passive_queue_type               priority_queues
% 2.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/0.99  --inst_passive_queues_freq              [25;2]
% 2.15/0.99  --inst_dismatching                      true
% 2.15/0.99  --inst_eager_unprocessed_to_passive     true
% 2.15/0.99  --inst_prop_sim_given                   true
% 2.15/0.99  --inst_prop_sim_new                     false
% 2.15/0.99  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       true
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  ------ Parsing...
% 2.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.00  ------ Proving...
% 2.15/1.00  ------ Problem Properties 
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  clauses                                 29
% 2.15/1.00  conjectures                             7
% 2.15/1.00  EPR                                     7
% 2.15/1.00  Horn                                    16
% 2.15/1.00  unary                                   10
% 2.15/1.00  binary                                  3
% 2.15/1.00  lits                                    89
% 2.15/1.00  lits eq                                 4
% 2.15/1.00  fd_pure                                 0
% 2.15/1.00  fd_pseudo                               0
% 2.15/1.00  fd_cond                                 0
% 2.15/1.00  fd_pseudo_cond                          3
% 2.15/1.00  AC symbols                              0
% 2.15/1.00  
% 2.15/1.00  ------ Schedule dynamic 5 is on 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  Current options:
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     none
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       false
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ Proving...
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS status Theorem for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  fof(f8,axiom,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f19,plain,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.15/1.00  
% 2.15/1.00  fof(f20,plain,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.00    inference(pure_predicate_removal,[],[f19])).
% 2.15/1.00  
% 2.15/1.00  fof(f30,plain,(
% 2.15/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f20])).
% 2.15/1.00  
% 2.15/1.00  fof(f31,plain,(
% 2.15/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f30])).
% 2.15/1.00  
% 2.15/1.00  fof(f49,plain,(
% 2.15/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f50,plain,(
% 2.15/1.00    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f49])).
% 2.15/1.00  
% 2.15/1.00  fof(f69,plain,(
% 2.15/1.00    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f50])).
% 2.15/1.00  
% 2.15/1.00  fof(f3,axiom,(
% 2.15/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f22,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f3])).
% 2.15/1.00  
% 2.15/1.00  fof(f63,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f22])).
% 2.15/1.00  
% 2.15/1.00  fof(f14,conjecture,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f15,negated_conjecture,(
% 2.15/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.15/1.00    inference(negated_conjecture,[],[f14])).
% 2.15/1.00  
% 2.15/1.00  fof(f42,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f15])).
% 2.15/1.00  
% 2.15/1.00  fof(f43,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f42])).
% 2.15/1.00  
% 2.15/1.00  fof(f54,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK5) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f53,plain,(
% 2.15/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK4,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK4),X3) & m1_subset_1(X3,u1_struct_0(sK4))) & r1_xboole_0(u1_struct_0(sK4),X1) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f52,plain,(
% 2.15/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,sK3),k2_tmap_1(X0,k6_tmap_1(X0,sK3),k7_tmap_1(X0,sK3),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f51,plain,(
% 2.15/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK2,X1),k2_tmap_1(sK2,k6_tmap_1(sK2,X1),k7_tmap_1(sK2,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f55,plain,(
% 2.15/1.00    (((~r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) & m1_subset_1(sK5,u1_struct_0(sK4))) & r1_xboole_0(u1_struct_0(sK4),sK3) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f54,f53,f52,f51])).
% 2.15/1.00  
% 2.15/1.00  fof(f86,plain,(
% 2.15/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f4,axiom,(
% 2.15/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f23,plain,(
% 2.15/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.15/1.00    inference(ennf_transformation,[],[f4])).
% 2.15/1.00  
% 2.15/1.00  fof(f24,plain,(
% 2.15/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.15/1.00    inference(flattening,[],[f23])).
% 2.15/1.00  
% 2.15/1.00  fof(f64,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f24])).
% 2.15/1.00  
% 2.15/1.00  fof(f2,axiom,(
% 2.15/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f16,plain,(
% 2.15/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.15/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 2.15/1.00  
% 2.15/1.00  fof(f21,plain,(
% 2.15/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.15/1.00    inference(ennf_transformation,[],[f16])).
% 2.15/1.00  
% 2.15/1.00  fof(f62,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f21])).
% 2.15/1.00  
% 2.15/1.00  fof(f85,plain,(
% 2.15/1.00    r1_xboole_0(u1_struct_0(sK4),sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f1,axiom,(
% 2.15/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f44,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/1.00    inference(nnf_transformation,[],[f1])).
% 2.15/1.00  
% 2.15/1.00  fof(f45,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/1.00    inference(flattening,[],[f44])).
% 2.15/1.00  
% 2.15/1.00  fof(f46,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/1.00    inference(rectify,[],[f45])).
% 2.15/1.00  
% 2.15/1.00  fof(f47,plain,(
% 2.15/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f48,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 2.15/1.00  
% 2.15/1.00  fof(f57,plain,(
% 2.15/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.15/1.00    inference(cnf_transformation,[],[f48])).
% 2.15/1.00  
% 2.15/1.00  fof(f89,plain,(
% 2.15/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.15/1.00    inference(equality_resolution,[],[f57])).
% 2.15/1.00  
% 2.15/1.00  fof(f11,axiom,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f17,plain,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 2.15/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.15/1.00  
% 2.15/1.00  fof(f36,plain,(
% 2.15/1.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f17])).
% 2.15/1.00  
% 2.15/1.00  fof(f37,plain,(
% 2.15/1.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f36])).
% 2.15/1.00  
% 2.15/1.00  fof(f75,plain,(
% 2.15/1.00    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f12,axiom,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f38,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f12])).
% 2.15/1.00  
% 2.15/1.00  fof(f39,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f38])).
% 2.15/1.00  
% 2.15/1.00  fof(f77,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f39])).
% 2.15/1.00  
% 2.15/1.00  fof(f13,axiom,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f40,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f13])).
% 2.15/1.00  
% 2.15/1.00  fof(f41,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f40])).
% 2.15/1.00  
% 2.15/1.00  fof(f78,plain,(
% 2.15/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f41])).
% 2.15/1.00  
% 2.15/1.00  fof(f91,plain,(
% 2.15/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(equality_resolution,[],[f78])).
% 2.15/1.00  
% 2.15/1.00  fof(f84,plain,(
% 2.15/1.00    m1_pre_topc(sK4,sK2)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f79,plain,(
% 2.15/1.00    ~v2_struct_0(sK2)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f80,plain,(
% 2.15/1.00    v2_pre_topc(sK2)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f81,plain,(
% 2.15/1.00    l1_pre_topc(sK2)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f83,plain,(
% 2.15/1.00    ~v2_struct_0(sK4)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f7,axiom,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f28,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f7])).
% 2.15/1.00  
% 2.15/1.00  fof(f29,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f28])).
% 2.15/1.00  
% 2.15/1.00  fof(f67,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f29])).
% 2.15/1.00  
% 2.15/1.00  fof(f87,plain,(
% 2.15/1.00    ~r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5)),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f82,plain,(
% 2.15/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.15/1.00    inference(cnf_transformation,[],[f55])).
% 2.15/1.00  
% 2.15/1.00  fof(f9,axiom,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f18,plain,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 2.15/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.15/1.00  
% 2.15/1.00  fof(f32,plain,(
% 2.15/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f18])).
% 2.15/1.00  
% 2.15/1.00  fof(f33,plain,(
% 2.15/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f32])).
% 2.15/1.00  
% 2.15/1.00  fof(f71,plain,(
% 2.15/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f33])).
% 2.15/1.00  
% 2.15/1.00  fof(f10,axiom,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f34,plain,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f10])).
% 2.15/1.00  
% 2.15/1.00  fof(f35,plain,(
% 2.15/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f34])).
% 2.15/1.00  
% 2.15/1.00  fof(f72,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f76,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f74,plain,(
% 2.15/1.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f73,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f68,plain,(
% 2.15/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f50])).
% 2.15/1.00  
% 2.15/1.00  fof(f5,axiom,(
% 2.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f25,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f5])).
% 2.15/1.00  
% 2.15/1.00  fof(f26,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.00    inference(flattening,[],[f25])).
% 2.15/1.00  
% 2.15/1.00  fof(f65,plain,(
% 2.15/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f26])).
% 2.15/1.00  
% 2.15/1.00  fof(f6,axiom,(
% 2.15/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f27,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f6])).
% 2.15/1.00  
% 2.15/1.00  fof(f66,plain,(
% 2.15/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f27])).
% 2.15/1.00  
% 2.15/1.00  cnf(c_12,plain,
% 2.15/1.00      ( v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0)
% 2.15/1.00      | ~ v1_xboole_0(sK1(X0)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3915,plain,
% 2.15/1.00      ( v2_struct_0(sK4)
% 2.15/1.00      | ~ l1_pre_topc(sK4)
% 2.15/1.00      | ~ v2_pre_topc(sK4)
% 2.15/1.00      | ~ v1_xboole_0(sK1(sK4)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_7,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.15/1.00      | ~ v1_xboole_0(X1)
% 2.15/1.00      | v1_xboole_0(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1869,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.15/1.00      | v1_xboole_0(X0)
% 2.15/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3194,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.15/1.00      | v1_xboole_0(sK1(sK4))
% 2.15/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_1869]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_24,negated_conjecture,
% 2.15/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1500,plain,
% 2.15/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_8,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1511,plain,
% 2.15/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.15/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.15/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1999,plain,
% 2.15/1.00      ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 2.15/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1500,c_1511]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6,plain,
% 2.15/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_25,negated_conjecture,
% 2.15/1.00      ( r1_xboole_0(u1_struct_0(sK4),sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_337,plain,
% 2.15/1.00      ( k4_xboole_0(X0,X1) = X0 | u1_struct_0(sK4) != X0 | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_338,plain,
% 2.15/1.00      ( k4_xboole_0(u1_struct_0(sK4),sK3) = u1_struct_0(sK4) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_337]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_4,plain,
% 2.15/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1514,plain,
% 2.15/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.15/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1991,plain,
% 2.15/1.00      ( r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 2.15/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_338,c_1514]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2789,plain,
% 2.15/1.00      ( r2_hidden(sK5,sK3) != iProver_top
% 2.15/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1999,c_1991]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2790,plain,
% 2.15/1.00      ( ~ r2_hidden(sK5,sK3) | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.15/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2789]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_20,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2585,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | ~ v2_struct_0(k6_tmap_1(sK2,sK3))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_21,plain,
% 2.15/1.00      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | r2_hidden(X2,X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1502,plain,
% 2.15/1.00      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) = iProver_top
% 2.15/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.15/1.00      | r2_hidden(X2,X1) = iProver_top
% 2.15/1.00      | v2_struct_0(X0) = iProver_top
% 2.15/1.00      | l1_pre_topc(X0) != iProver_top
% 2.15/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_22,plain,
% 2.15/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.15/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.00      | ~ m1_pre_topc(X4,X0)
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.00      | ~ v1_funct_1(X2)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | v2_struct_0(X4)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_26,negated_conjecture,
% 2.15/1.00      ( m1_pre_topc(sK4,sK2) ),
% 2.15/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_510,plain,
% 2.15/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.15/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.00      | ~ v1_funct_1(X2)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | v2_struct_0(X4)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X1)
% 2.15/1.00      | sK2 != X0
% 2.15/1.00      | sK4 != X4 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_511,plain,
% 2.15/1.00      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 2.15/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 2.15/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.15/1.00      | ~ v1_funct_1(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | v2_struct_0(sK4)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_510]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_31,negated_conjecture,
% 2.15/1.00      ( ~ v2_struct_0(sK2) ),
% 2.15/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_30,negated_conjecture,
% 2.15/1.00      ( v2_pre_topc(sK2) ),
% 2.15/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_29,negated_conjecture,
% 2.15/1.00      ( l1_pre_topc(sK2) ),
% 2.15/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_27,negated_conjecture,
% 2.15/1.00      ( ~ v2_struct_0(sK4) ),
% 2.15/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_515,plain,
% 2.15/1.00      ( ~ v2_pre_topc(X0)
% 2.15/1.00      | ~ r1_tmap_1(sK2,X0,X1,X2)
% 2.15/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 2.15/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.15/1.00      | ~ v1_funct_1(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_511,c_31,c_30,c_29,c_27]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_516,plain,
% 2.15/1.00      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 2.15/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 2.15/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.15/1.00      | ~ v1_funct_1(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(renaming,[status(thm)],[c_515]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_11,plain,
% 2.15/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.15/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_470,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.00      | m1_subset_1(X0,u1_struct_0(X2))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | v2_struct_0(X2)
% 2.15/1.00      | ~ l1_pre_topc(X2)
% 2.15/1.00      | sK2 != X2
% 2.15/1.00      | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_471,plain,
% 2.15/1.00      ( m1_subset_1(X0,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | v2_struct_0(sK4)
% 2.15/1.00      | ~ l1_pre_topc(sK2) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_475,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.15/1.00      | m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_471,c_31,c_29,c_27]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_476,plain,
% 2.15/1.00      ( m1_subset_1(X0,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.15/1.00      inference(renaming,[status(thm)],[c_475]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_531,plain,
% 2.15/1.00      ( ~ r1_tmap_1(sK2,X0,X1,X2)
% 2.15/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2)
% 2.15/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.15/1.00      | ~ v1_funct_1(X1)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(forward_subsumption_resolution,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_516,c_476]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1491,plain,
% 2.15/1.00      ( r1_tmap_1(sK2,X0,X1,X2) != iProver_top
% 2.15/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,X1,sK4),X2) = iProver_top
% 2.15/1.00      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 2.15/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 2.15/1.00      | v1_funct_1(X1) != iProver_top
% 2.15/1.00      | v2_struct_0(X0) = iProver_top
% 2.15/1.00      | l1_pre_topc(X0) != iProver_top
% 2.15/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_23,negated_conjecture,
% 2.15/1.00      ( ~ r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) ),
% 2.15/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1501,plain,
% 2.15/1.00      ( r1_tmap_1(sK4,k6_tmap_1(sK2,sK3),k2_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK4),sK5) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1884,plain,
% 2.15/1.00      ( r1_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK5) != iProver_top
% 2.15/1.00      | v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))))) != iProver_top
% 2.15/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.15/1.00      | v1_funct_1(k7_tmap_1(sK2,sK3)) != iProver_top
% 2.15/1.00      | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top
% 2.15/1.00      | l1_pre_topc(k6_tmap_1(sK2,sK3)) != iProver_top
% 2.15/1.00      | v2_pre_topc(k6_tmap_1(sK2,sK3)) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1491,c_1501]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_32,plain,
% 2.15/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_33,plain,
% 2.15/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_34,plain,
% 2.15/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_28,negated_conjecture,
% 2.15/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.15/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_35,plain,
% 2.15/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_39,plain,
% 2.15/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_14,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.15/1.00      | ~ v2_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1789,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | l1_pre_topc(k6_tmap_1(sK2,sK3))
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1790,plain,
% 2.15/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(k6_tmap_1(sK2,sK3)) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_18,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1797,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | v1_funct_1(k7_tmap_1(sK2,sK3))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1798,plain,
% 2.15/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | v1_funct_1(k7_tmap_1(sK2,sK3)) = iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_19,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X1)
% 2.15/1.00      | v2_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1805,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | v2_pre_topc(k6_tmap_1(sK2,sK3))
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1806,plain,
% 2.15/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(k6_tmap_1(sK2,sK3)) = iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_16,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1831,plain,
% 2.15/1.00      ( m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3)))))
% 2.15/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1832,plain,
% 2.15/1.00      ( m1_subset_1(k7_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))))) = iProver_top
% 2.15/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1831]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_17,plain,
% 2.15/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1839,plain,
% 2.15/1.00      ( v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3)))
% 2.15/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1840,plain,
% 2.15/1.00      ( v1_funct_2(k7_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK3))) = iProver_top
% 2.15/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1839]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2438,plain,
% 2.15/1.00      ( r1_tmap_1(sK2,k6_tmap_1(sK2,sK3),k7_tmap_1(sK2,sK3),sK5) != iProver_top
% 2.15/1.00      | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_1884,c_32,c_33,c_34,c_35,c_39,c_1790,c_1798,c_1806,
% 2.15/1.00                 c_1832,c_1840]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2539,plain,
% 2.15/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.15/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.15/1.00      | r2_hidden(sK5,sK3) = iProver_top
% 2.15/1.00      | v2_struct_0(k6_tmap_1(sK2,sK3)) = iProver_top
% 2.15/1.00      | v2_struct_0(sK2) = iProver_top
% 2.15/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1502,c_2438]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2540,plain,
% 2.15/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.15/1.00      | r2_hidden(sK5,sK3)
% 2.15/1.00      | v2_struct_0(k6_tmap_1(sK2,sK3))
% 2.15/1.00      | v2_struct_0(sK2)
% 2.15/1.00      | ~ l1_pre_topc(sK2)
% 2.15/1.00      | ~ v2_pre_topc(sK2) ),
% 2.15/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2539]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_13,plain,
% 2.15/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1983,plain,
% 2.15/1.00      ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.15/1.00      | v2_struct_0(sK4)
% 2.15/1.00      | ~ l1_pre_topc(sK4)
% 2.15/1.00      | ~ v2_pre_topc(sK4) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1766,plain,
% 2.15/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2))
% 2.15/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_476]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_9,plain,
% 2.15/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.00      | ~ l1_pre_topc(X1)
% 2.15/1.00      | ~ v2_pre_topc(X1)
% 2.15/1.00      | v2_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_499,plain,
% 2.15/1.00      ( ~ l1_pre_topc(X0)
% 2.15/1.00      | ~ v2_pre_topc(X0)
% 2.15/1.00      | v2_pre_topc(X1)
% 2.15/1.00      | sK2 != X0
% 2.15/1.00      | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_500,plain,
% 2.15/1.00      ( ~ l1_pre_topc(sK2) | ~ v2_pre_topc(sK2) | v2_pre_topc(sK4) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_499]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_10,plain,
% 2.15/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_488,plain,
% 2.15/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_489,plain,
% 2.15/1.00      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_488]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(contradiction,plain,
% 2.15/1.00      ( $false ),
% 2.15/1.00      inference(minisat,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_3915,c_3194,c_2790,c_2585,c_2540,c_1983,c_1766,c_500,
% 2.15/1.00                 c_489,c_24,c_27,c_28,c_29,c_30,c_31]) ).
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  ------                               Statistics
% 2.15/1.00  
% 2.15/1.00  ------ General
% 2.15/1.00  
% 2.15/1.00  abstr_ref_over_cycles:                  0
% 2.15/1.00  abstr_ref_under_cycles:                 0
% 2.15/1.00  gc_basic_clause_elim:                   0
% 2.15/1.00  forced_gc_time:                         0
% 2.15/1.00  parsing_time:                           0.01
% 2.15/1.00  unif_index_cands_time:                  0.
% 2.15/1.00  unif_index_add_time:                    0.
% 2.15/1.00  orderings_time:                         0.
% 2.15/1.00  out_proof_time:                         0.01
% 2.15/1.00  total_time:                             0.157
% 2.15/1.00  num_of_symbols:                         55
% 2.15/1.00  num_of_terms:                           3669
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing
% 2.15/1.00  
% 2.15/1.00  num_of_splits:                          0
% 2.15/1.00  num_of_split_atoms:                     0
% 2.15/1.00  num_of_reused_defs:                     0
% 2.15/1.00  num_eq_ax_congr_red:                    14
% 2.15/1.00  num_of_sem_filtered_clauses:            1
% 2.15/1.00  num_of_subtypes:                        0
% 2.15/1.00  monotx_restored_types:                  0
% 2.15/1.00  sat_num_of_epr_types:                   0
% 2.15/1.00  sat_num_of_non_cyclic_types:            0
% 2.15/1.00  sat_guarded_non_collapsed_types:        0
% 2.15/1.00  num_pure_diseq_elim:                    0
% 2.15/1.00  simp_replaced_by:                       0
% 2.15/1.00  res_preprocessed:                       155
% 2.15/1.00  prep_upred:                             0
% 2.15/1.00  prep_unflattend:                        16
% 2.15/1.00  smt_new_axioms:                         0
% 2.15/1.00  pred_elim_cands:                        9
% 2.15/1.00  pred_elim:                              2
% 2.15/1.00  pred_elim_cl:                           2
% 2.15/1.00  pred_elim_cycles:                       8
% 2.15/1.00  merged_defs:                            0
% 2.15/1.00  merged_defs_ncl:                        0
% 2.15/1.00  bin_hyper_res:                          0
% 2.15/1.00  prep_cycles:                            4
% 2.15/1.00  pred_elim_time:                         0.014
% 2.15/1.00  splitting_time:                         0.
% 2.15/1.00  sem_filter_time:                        0.
% 2.15/1.00  monotx_time:                            0.
% 2.15/1.00  subtype_inf_time:                       0.
% 2.15/1.00  
% 2.15/1.00  ------ Problem properties
% 2.15/1.00  
% 2.15/1.00  clauses:                                29
% 2.15/1.00  conjectures:                            7
% 2.15/1.00  epr:                                    7
% 2.15/1.00  horn:                                   16
% 2.15/1.00  ground:                                 10
% 2.15/1.00  unary:                                  10
% 2.15/1.00  binary:                                 3
% 2.15/1.00  lits:                                   89
% 2.15/1.00  lits_eq:                                4
% 2.15/1.00  fd_pure:                                0
% 2.15/1.00  fd_pseudo:                              0
% 2.15/1.00  fd_cond:                                0
% 2.15/1.00  fd_pseudo_cond:                         3
% 2.15/1.00  ac_symbols:                             0
% 2.15/1.00  
% 2.15/1.00  ------ Propositional Solver
% 2.15/1.00  
% 2.15/1.00  prop_solver_calls:                      27
% 2.15/1.00  prop_fast_solver_calls:                 1280
% 2.15/1.00  smt_solver_calls:                       0
% 2.15/1.00  smt_fast_solver_calls:                  0
% 2.15/1.00  prop_num_of_clauses:                    1231
% 2.15/1.00  prop_preprocess_simplified:             5261
% 2.15/1.00  prop_fo_subsumed:                       36
% 2.15/1.00  prop_solver_time:                       0.
% 2.15/1.00  smt_solver_time:                        0.
% 2.15/1.00  smt_fast_solver_time:                   0.
% 2.15/1.00  prop_fast_solver_time:                  0.
% 2.15/1.00  prop_unsat_core_time:                   0.
% 2.15/1.00  
% 2.15/1.00  ------ QBF
% 2.15/1.00  
% 2.15/1.00  qbf_q_res:                              0
% 2.15/1.00  qbf_num_tautologies:                    0
% 2.15/1.00  qbf_prep_cycles:                        0
% 2.15/1.00  
% 2.15/1.00  ------ BMC1
% 2.15/1.00  
% 2.15/1.00  bmc1_current_bound:                     -1
% 2.15/1.00  bmc1_last_solved_bound:                 -1
% 2.15/1.00  bmc1_unsat_core_size:                   -1
% 2.15/1.00  bmc1_unsat_core_parents_size:           -1
% 2.15/1.00  bmc1_merge_next_fun:                    0
% 2.15/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation
% 2.15/1.00  
% 2.15/1.00  inst_num_of_clauses:                    353
% 2.15/1.00  inst_num_in_passive:                    141
% 2.15/1.00  inst_num_in_active:                     199
% 2.15/1.00  inst_num_in_unprocessed:                12
% 2.15/1.00  inst_num_of_loops:                      233
% 2.15/1.00  inst_num_of_learning_restarts:          0
% 2.15/1.00  inst_num_moves_active_passive:          30
% 2.15/1.00  inst_lit_activity:                      0
% 2.15/1.00  inst_lit_activity_moves:                0
% 2.15/1.00  inst_num_tautologies:                   0
% 2.15/1.00  inst_num_prop_implied:                  0
% 2.15/1.00  inst_num_existing_simplified:           0
% 2.15/1.00  inst_num_eq_res_simplified:             0
% 2.15/1.00  inst_num_child_elim:                    0
% 2.15/1.00  inst_num_of_dismatching_blockings:      40
% 2.15/1.00  inst_num_of_non_proper_insts:           284
% 2.15/1.00  inst_num_of_duplicates:                 0
% 2.15/1.00  inst_inst_num_from_inst_to_res:         0
% 2.15/1.00  inst_dismatching_checking_time:         0.
% 2.15/1.00  
% 2.15/1.00  ------ Resolution
% 2.15/1.00  
% 2.15/1.00  res_num_of_clauses:                     0
% 2.15/1.00  res_num_in_passive:                     0
% 2.15/1.00  res_num_in_active:                      0
% 2.15/1.00  res_num_of_loops:                       159
% 2.15/1.00  res_forward_subset_subsumed:            14
% 2.15/1.00  res_backward_subset_subsumed:           0
% 2.15/1.00  res_forward_subsumed:                   0
% 2.15/1.00  res_backward_subsumed:                  0
% 2.15/1.00  res_forward_subsumption_resolution:     5
% 2.15/1.00  res_backward_subsumption_resolution:    0
% 2.15/1.00  res_clause_to_clause_subsumption:       208
% 2.15/1.00  res_orphan_elimination:                 0
% 2.15/1.00  res_tautology_del:                      43
% 2.15/1.00  res_num_eq_res_simplified:              0
% 2.15/1.00  res_num_sel_changes:                    0
% 2.15/1.00  res_moves_from_active_to_pass:          0
% 2.15/1.00  
% 2.15/1.00  ------ Superposition
% 2.15/1.00  
% 2.15/1.00  sup_time_total:                         0.
% 2.15/1.00  sup_time_generating:                    0.
% 2.15/1.00  sup_time_sim_full:                      0.
% 2.15/1.00  sup_time_sim_immed:                     0.
% 2.15/1.00  
% 2.15/1.00  sup_num_of_clauses:                     64
% 2.15/1.00  sup_num_in_active:                      46
% 2.15/1.00  sup_num_in_passive:                     18
% 2.15/1.00  sup_num_of_loops:                       46
% 2.15/1.00  sup_fw_superposition:                   24
% 2.15/1.00  sup_bw_superposition:                   21
% 2.15/1.00  sup_immediate_simplified:               6
% 2.15/1.00  sup_given_eliminated:                   0
% 2.15/1.00  comparisons_done:                       0
% 2.15/1.00  comparisons_avoided:                    0
% 2.15/1.00  
% 2.15/1.00  ------ Simplifications
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  sim_fw_subset_subsumed:                 0
% 2.15/1.00  sim_bw_subset_subsumed:                 0
% 2.15/1.00  sim_fw_subsumed:                        4
% 2.15/1.00  sim_bw_subsumed:                        0
% 2.15/1.00  sim_fw_subsumption_res:                 1
% 2.15/1.00  sim_bw_subsumption_res:                 0
% 2.15/1.00  sim_tautology_del:                      6
% 2.15/1.00  sim_eq_tautology_del:                   0
% 2.15/1.00  sim_eq_res_simp:                        1
% 2.15/1.00  sim_fw_demodulated:                     0
% 2.15/1.00  sim_bw_demodulated:                     0
% 2.15/1.00  sim_light_normalised:                   1
% 2.15/1.00  sim_joinable_taut:                      0
% 2.15/1.00  sim_joinable_simp:                      0
% 2.15/1.00  sim_ac_normalised:                      0
% 2.15/1.00  sim_smt_subsumption:                    0
% 2.15/1.00  
%------------------------------------------------------------------------------
