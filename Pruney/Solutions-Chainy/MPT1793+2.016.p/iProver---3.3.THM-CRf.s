%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:58 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 499 expanded)
%              Number of clauses        :   81 ( 116 expanded)
%              Number of leaves         :   18 ( 173 expanded)
%              Depth                    :   16
%              Number of atoms          :  764 (3613 expanded)
%              Number of equality atoms :  121 ( 130 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK4)
        & m1_subset_1(sK4,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK3,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),X3)
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & r1_xboole_0(u1_struct_0(sK3),X1)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
                ( ~ r1_tmap_1(X2,k6_tmap_1(X0,sK2),k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK1,X1),k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & r1_xboole_0(u1_struct_0(sK3),sK2)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f48,f47,f46,f45])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1909,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3638,plain,
    ( v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1915])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1912,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1921,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2923,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1921])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_594,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_595,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_596,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_2182,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2183,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_409,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_2239,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_2240,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_3279,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_34,c_36,c_39,c_596,c_2183,c_2240])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1911,plain,
    ( r1_xboole_0(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1922,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2262,plain,
    ( k4_xboole_0(u1_struct_0(sK3),sK2) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1911,c_1922])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1926,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2861,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2262,c_1926])).

cnf(c_3397,plain,
    ( r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_2861])).

cnf(c_21,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2234,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK4,X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3259,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK4,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_3260,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK4,sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_22,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_605,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_606,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_610,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_31,c_30,c_29,c_27])).

cnf(c_611,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK1 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_577,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_31,c_29,c_27])).

cnf(c_582,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_581])).

cnf(c_626,plain,
    ( ~ r1_tmap_1(sK1,X0,X1,X2)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_611,c_582])).

cnf(c_1902,plain,
    ( r1_tmap_1(sK1,X0,X1,X2) != iProver_top
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1913,plain,
    ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2257,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1913])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2189,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2191,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2192,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2191])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2211,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2212,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2211])).

cnf(c_17,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2214,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2215,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_2782,plain,
    ( v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
    | r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2257,c_32,c_33,c_34,c_35,c_39,c_2189,c_2192,c_2195,c_2212,c_2215])).

cnf(c_2783,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top
    | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2782])).

cnf(c_2171,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_2172,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3638,c_3397,c_3260,c_2783,c_2172,c_39,c_35,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.94/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.01  
% 1.94/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.94/1.01  
% 1.94/1.01  ------  iProver source info
% 1.94/1.01  
% 1.94/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.94/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.94/1.01  git: non_committed_changes: false
% 1.94/1.01  git: last_make_outside_of_git: false
% 1.94/1.01  
% 1.94/1.01  ------ 
% 1.94/1.01  
% 1.94/1.01  ------ Input Options
% 1.94/1.01  
% 1.94/1.01  --out_options                           all
% 1.94/1.01  --tptp_safe_out                         true
% 1.94/1.01  --problem_path                          ""
% 1.94/1.01  --include_path                          ""
% 1.94/1.01  --clausifier                            res/vclausify_rel
% 1.94/1.01  --clausifier_options                    --mode clausify
% 1.94/1.01  --stdin                                 false
% 1.94/1.01  --stats_out                             all
% 1.94/1.01  
% 1.94/1.01  ------ General Options
% 1.94/1.01  
% 1.94/1.01  --fof                                   false
% 1.94/1.01  --time_out_real                         305.
% 1.94/1.01  --time_out_virtual                      -1.
% 1.94/1.01  --symbol_type_check                     false
% 1.94/1.01  --clausify_out                          false
% 1.94/1.01  --sig_cnt_out                           false
% 1.94/1.01  --trig_cnt_out                          false
% 1.94/1.01  --trig_cnt_out_tolerance                1.
% 1.94/1.01  --trig_cnt_out_sk_spl                   false
% 1.94/1.01  --abstr_cl_out                          false
% 1.94/1.01  
% 1.94/1.01  ------ Global Options
% 1.94/1.01  
% 1.94/1.01  --schedule                              default
% 1.94/1.01  --add_important_lit                     false
% 1.94/1.01  --prop_solver_per_cl                    1000
% 1.94/1.01  --min_unsat_core                        false
% 1.94/1.01  --soft_assumptions                      false
% 1.94/1.01  --soft_lemma_size                       3
% 1.94/1.01  --prop_impl_unit_size                   0
% 1.94/1.01  --prop_impl_unit                        []
% 1.94/1.01  --share_sel_clauses                     true
% 1.94/1.01  --reset_solvers                         false
% 1.94/1.01  --bc_imp_inh                            [conj_cone]
% 1.94/1.01  --conj_cone_tolerance                   3.
% 1.94/1.01  --extra_neg_conj                        none
% 1.94/1.01  --large_theory_mode                     true
% 1.94/1.01  --prolific_symb_bound                   200
% 1.94/1.01  --lt_threshold                          2000
% 1.94/1.01  --clause_weak_htbl                      true
% 1.94/1.01  --gc_record_bc_elim                     false
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing Options
% 1.94/1.01  
% 1.94/1.01  --preprocessing_flag                    true
% 1.94/1.01  --time_out_prep_mult                    0.1
% 1.94/1.01  --splitting_mode                        input
% 1.94/1.01  --splitting_grd                         true
% 1.94/1.01  --splitting_cvd                         false
% 1.94/1.01  --splitting_cvd_svl                     false
% 1.94/1.01  --splitting_nvd                         32
% 1.94/1.01  --sub_typing                            true
% 1.94/1.01  --prep_gs_sim                           true
% 1.94/1.01  --prep_unflatten                        true
% 1.94/1.01  --prep_res_sim                          true
% 1.94/1.01  --prep_upred                            true
% 1.94/1.01  --prep_sem_filter                       exhaustive
% 1.94/1.01  --prep_sem_filter_out                   false
% 1.94/1.01  --pred_elim                             true
% 1.94/1.01  --res_sim_input                         true
% 1.94/1.01  --eq_ax_congr_red                       true
% 1.94/1.01  --pure_diseq_elim                       true
% 1.94/1.01  --brand_transform                       false
% 1.94/1.01  --non_eq_to_eq                          false
% 1.94/1.01  --prep_def_merge                        true
% 1.94/1.01  --prep_def_merge_prop_impl              false
% 1.94/1.01  --prep_def_merge_mbd                    true
% 1.94/1.01  --prep_def_merge_tr_red                 false
% 1.94/1.01  --prep_def_merge_tr_cl                  false
% 1.94/1.01  --smt_preprocessing                     true
% 1.94/1.01  --smt_ac_axioms                         fast
% 1.94/1.01  --preprocessed_out                      false
% 1.94/1.01  --preprocessed_stats                    false
% 1.94/1.01  
% 1.94/1.01  ------ Abstraction refinement Options
% 1.94/1.01  
% 1.94/1.01  --abstr_ref                             []
% 1.94/1.01  --abstr_ref_prep                        false
% 1.94/1.01  --abstr_ref_until_sat                   false
% 1.94/1.01  --abstr_ref_sig_restrict                funpre
% 1.94/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/1.01  --abstr_ref_under                       []
% 1.94/1.01  
% 1.94/1.01  ------ SAT Options
% 1.94/1.01  
% 1.94/1.01  --sat_mode                              false
% 1.94/1.01  --sat_fm_restart_options                ""
% 1.94/1.01  --sat_gr_def                            false
% 1.94/1.01  --sat_epr_types                         true
% 1.94/1.01  --sat_non_cyclic_types                  false
% 1.94/1.01  --sat_finite_models                     false
% 1.94/1.01  --sat_fm_lemmas                         false
% 1.94/1.01  --sat_fm_prep                           false
% 1.94/1.01  --sat_fm_uc_incr                        true
% 1.94/1.01  --sat_out_model                         small
% 1.94/1.01  --sat_out_clauses                       false
% 1.94/1.01  
% 1.94/1.01  ------ QBF Options
% 1.94/1.01  
% 1.94/1.01  --qbf_mode                              false
% 1.94/1.01  --qbf_elim_univ                         false
% 1.94/1.01  --qbf_dom_inst                          none
% 1.94/1.01  --qbf_dom_pre_inst                      false
% 1.94/1.01  --qbf_sk_in                             false
% 1.94/1.01  --qbf_pred_elim                         true
% 1.94/1.01  --qbf_split                             512
% 1.94/1.01  
% 1.94/1.01  ------ BMC1 Options
% 1.94/1.01  
% 1.94/1.01  --bmc1_incremental                      false
% 1.94/1.01  --bmc1_axioms                           reachable_all
% 1.94/1.01  --bmc1_min_bound                        0
% 1.94/1.01  --bmc1_max_bound                        -1
% 1.94/1.01  --bmc1_max_bound_default                -1
% 1.94/1.01  --bmc1_symbol_reachability              true
% 1.94/1.01  --bmc1_property_lemmas                  false
% 1.94/1.01  --bmc1_k_induction                      false
% 1.94/1.01  --bmc1_non_equiv_states                 false
% 1.94/1.01  --bmc1_deadlock                         false
% 1.94/1.01  --bmc1_ucm                              false
% 1.94/1.01  --bmc1_add_unsat_core                   none
% 1.94/1.01  --bmc1_unsat_core_children              false
% 1.94/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/1.01  --bmc1_out_stat                         full
% 1.94/1.01  --bmc1_ground_init                      false
% 1.94/1.01  --bmc1_pre_inst_next_state              false
% 1.94/1.01  --bmc1_pre_inst_state                   false
% 1.94/1.01  --bmc1_pre_inst_reach_state             false
% 1.94/1.01  --bmc1_out_unsat_core                   false
% 1.94/1.01  --bmc1_aig_witness_out                  false
% 1.94/1.01  --bmc1_verbose                          false
% 1.94/1.01  --bmc1_dump_clauses_tptp                false
% 1.94/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.94/1.01  --bmc1_dump_file                        -
% 1.94/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.94/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.94/1.01  --bmc1_ucm_extend_mode                  1
% 1.94/1.01  --bmc1_ucm_init_mode                    2
% 1.94/1.01  --bmc1_ucm_cone_mode                    none
% 1.94/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.94/1.01  --bmc1_ucm_relax_model                  4
% 1.94/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.94/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/1.01  --bmc1_ucm_layered_model                none
% 1.94/1.01  --bmc1_ucm_max_lemma_size               10
% 1.94/1.01  
% 1.94/1.01  ------ AIG Options
% 1.94/1.01  
% 1.94/1.01  --aig_mode                              false
% 1.94/1.01  
% 1.94/1.01  ------ Instantiation Options
% 1.94/1.01  
% 1.94/1.01  --instantiation_flag                    true
% 1.94/1.01  --inst_sos_flag                         false
% 1.94/1.01  --inst_sos_phase                        true
% 1.94/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/1.01  --inst_lit_sel_side                     num_symb
% 1.94/1.01  --inst_solver_per_active                1400
% 1.94/1.01  --inst_solver_calls_frac                1.
% 1.94/1.01  --inst_passive_queue_type               priority_queues
% 1.94/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/1.01  --inst_passive_queues_freq              [25;2]
% 1.94/1.01  --inst_dismatching                      true
% 1.94/1.01  --inst_eager_unprocessed_to_passive     true
% 1.94/1.01  --inst_prop_sim_given                   true
% 1.94/1.01  --inst_prop_sim_new                     false
% 1.94/1.01  --inst_subs_new                         false
% 1.94/1.01  --inst_eq_res_simp                      false
% 1.94/1.01  --inst_subs_given                       false
% 1.94/1.01  --inst_orphan_elimination               true
% 1.94/1.01  --inst_learning_loop_flag               true
% 1.94/1.01  --inst_learning_start                   3000
% 1.94/1.01  --inst_learning_factor                  2
% 1.94/1.01  --inst_start_prop_sim_after_learn       3
% 1.94/1.01  --inst_sel_renew                        solver
% 1.94/1.01  --inst_lit_activity_flag                true
% 1.94/1.01  --inst_restr_to_given                   false
% 1.94/1.01  --inst_activity_threshold               500
% 1.94/1.01  --inst_out_proof                        true
% 1.94/1.01  
% 1.94/1.01  ------ Resolution Options
% 1.94/1.01  
% 1.94/1.01  --resolution_flag                       true
% 1.94/1.01  --res_lit_sel                           adaptive
% 1.94/1.01  --res_lit_sel_side                      none
% 1.94/1.01  --res_ordering                          kbo
% 1.94/1.01  --res_to_prop_solver                    active
% 1.94/1.01  --res_prop_simpl_new                    false
% 1.94/1.01  --res_prop_simpl_given                  true
% 1.94/1.01  --res_passive_queue_type                priority_queues
% 1.94/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/1.01  --res_passive_queues_freq               [15;5]
% 1.94/1.01  --res_forward_subs                      full
% 1.94/1.01  --res_backward_subs                     full
% 1.94/1.01  --res_forward_subs_resolution           true
% 1.94/1.01  --res_backward_subs_resolution          true
% 1.94/1.01  --res_orphan_elimination                true
% 1.94/1.01  --res_time_limit                        2.
% 1.94/1.01  --res_out_proof                         true
% 1.94/1.01  
% 1.94/1.01  ------ Superposition Options
% 1.94/1.01  
% 1.94/1.01  --superposition_flag                    true
% 1.94/1.01  --sup_passive_queue_type                priority_queues
% 1.94/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.94/1.01  --demod_completeness_check              fast
% 1.94/1.01  --demod_use_ground                      true
% 1.94/1.01  --sup_to_prop_solver                    passive
% 1.94/1.01  --sup_prop_simpl_new                    true
% 1.94/1.01  --sup_prop_simpl_given                  true
% 1.94/1.01  --sup_fun_splitting                     false
% 1.94/1.01  --sup_smt_interval                      50000
% 1.94/1.01  
% 1.94/1.01  ------ Superposition Simplification Setup
% 1.94/1.01  
% 1.94/1.01  --sup_indices_passive                   []
% 1.94/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_full_bw                           [BwDemod]
% 1.94/1.01  --sup_immed_triv                        [TrivRules]
% 1.94/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_immed_bw_main                     []
% 1.94/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.01  
% 1.94/1.01  ------ Combination Options
% 1.94/1.01  
% 1.94/1.01  --comb_res_mult                         3
% 1.94/1.01  --comb_sup_mult                         2
% 1.94/1.01  --comb_inst_mult                        10
% 1.94/1.01  
% 1.94/1.01  ------ Debug Options
% 1.94/1.01  
% 1.94/1.01  --dbg_backtrace                         false
% 1.94/1.01  --dbg_dump_prop_clauses                 false
% 1.94/1.01  --dbg_dump_prop_clauses_file            -
% 1.94/1.01  --dbg_out_stat                          false
% 1.94/1.01  ------ Parsing...
% 1.94/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.94/1.01  ------ Proving...
% 1.94/1.01  ------ Problem Properties 
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  clauses                                 29
% 1.94/1.01  conjectures                             8
% 1.94/1.01  EPR                                     7
% 1.94/1.01  Horn                                    17
% 1.94/1.01  unary                                   9
% 1.94/1.01  binary                                  6
% 1.94/1.01  lits                                    86
% 1.94/1.01  lits eq                                 5
% 1.94/1.01  fd_pure                                 0
% 1.94/1.01  fd_pseudo                               0
% 1.94/1.01  fd_cond                                 0
% 1.94/1.01  fd_pseudo_cond                          3
% 1.94/1.01  AC symbols                              0
% 1.94/1.01  
% 1.94/1.01  ------ Schedule dynamic 5 is on 
% 1.94/1.01  
% 1.94/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  ------ 
% 1.94/1.01  Current options:
% 1.94/1.01  ------ 
% 1.94/1.01  
% 1.94/1.01  ------ Input Options
% 1.94/1.01  
% 1.94/1.01  --out_options                           all
% 1.94/1.01  --tptp_safe_out                         true
% 1.94/1.01  --problem_path                          ""
% 1.94/1.01  --include_path                          ""
% 1.94/1.01  --clausifier                            res/vclausify_rel
% 1.94/1.01  --clausifier_options                    --mode clausify
% 1.94/1.01  --stdin                                 false
% 1.94/1.01  --stats_out                             all
% 1.94/1.01  
% 1.94/1.01  ------ General Options
% 1.94/1.01  
% 1.94/1.01  --fof                                   false
% 1.94/1.01  --time_out_real                         305.
% 1.94/1.01  --time_out_virtual                      -1.
% 1.94/1.01  --symbol_type_check                     false
% 1.94/1.01  --clausify_out                          false
% 1.94/1.01  --sig_cnt_out                           false
% 1.94/1.01  --trig_cnt_out                          false
% 1.94/1.01  --trig_cnt_out_tolerance                1.
% 1.94/1.01  --trig_cnt_out_sk_spl                   false
% 1.94/1.01  --abstr_cl_out                          false
% 1.94/1.01  
% 1.94/1.01  ------ Global Options
% 1.94/1.01  
% 1.94/1.01  --schedule                              default
% 1.94/1.01  --add_important_lit                     false
% 1.94/1.01  --prop_solver_per_cl                    1000
% 1.94/1.01  --min_unsat_core                        false
% 1.94/1.01  --soft_assumptions                      false
% 1.94/1.01  --soft_lemma_size                       3
% 1.94/1.01  --prop_impl_unit_size                   0
% 1.94/1.01  --prop_impl_unit                        []
% 1.94/1.01  --share_sel_clauses                     true
% 1.94/1.01  --reset_solvers                         false
% 1.94/1.01  --bc_imp_inh                            [conj_cone]
% 1.94/1.01  --conj_cone_tolerance                   3.
% 1.94/1.01  --extra_neg_conj                        none
% 1.94/1.01  --large_theory_mode                     true
% 1.94/1.01  --prolific_symb_bound                   200
% 1.94/1.01  --lt_threshold                          2000
% 1.94/1.01  --clause_weak_htbl                      true
% 1.94/1.01  --gc_record_bc_elim                     false
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing Options
% 1.94/1.01  
% 1.94/1.01  --preprocessing_flag                    true
% 1.94/1.01  --time_out_prep_mult                    0.1
% 1.94/1.01  --splitting_mode                        input
% 1.94/1.01  --splitting_grd                         true
% 1.94/1.01  --splitting_cvd                         false
% 1.94/1.01  --splitting_cvd_svl                     false
% 1.94/1.01  --splitting_nvd                         32
% 1.94/1.01  --sub_typing                            true
% 1.94/1.01  --prep_gs_sim                           true
% 1.94/1.01  --prep_unflatten                        true
% 1.94/1.01  --prep_res_sim                          true
% 1.94/1.01  --prep_upred                            true
% 1.94/1.01  --prep_sem_filter                       exhaustive
% 1.94/1.01  --prep_sem_filter_out                   false
% 1.94/1.01  --pred_elim                             true
% 1.94/1.01  --res_sim_input                         true
% 1.94/1.01  --eq_ax_congr_red                       true
% 1.94/1.01  --pure_diseq_elim                       true
% 1.94/1.01  --brand_transform                       false
% 1.94/1.01  --non_eq_to_eq                          false
% 1.94/1.01  --prep_def_merge                        true
% 1.94/1.01  --prep_def_merge_prop_impl              false
% 1.94/1.01  --prep_def_merge_mbd                    true
% 1.94/1.01  --prep_def_merge_tr_red                 false
% 1.94/1.01  --prep_def_merge_tr_cl                  false
% 1.94/1.01  --smt_preprocessing                     true
% 1.94/1.01  --smt_ac_axioms                         fast
% 1.94/1.01  --preprocessed_out                      false
% 1.94/1.01  --preprocessed_stats                    false
% 1.94/1.01  
% 1.94/1.01  ------ Abstraction refinement Options
% 1.94/1.01  
% 1.94/1.01  --abstr_ref                             []
% 1.94/1.01  --abstr_ref_prep                        false
% 1.94/1.01  --abstr_ref_until_sat                   false
% 1.94/1.01  --abstr_ref_sig_restrict                funpre
% 1.94/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/1.01  --abstr_ref_under                       []
% 1.94/1.01  
% 1.94/1.01  ------ SAT Options
% 1.94/1.01  
% 1.94/1.01  --sat_mode                              false
% 1.94/1.01  --sat_fm_restart_options                ""
% 1.94/1.01  --sat_gr_def                            false
% 1.94/1.01  --sat_epr_types                         true
% 1.94/1.01  --sat_non_cyclic_types                  false
% 1.94/1.01  --sat_finite_models                     false
% 1.94/1.01  --sat_fm_lemmas                         false
% 1.94/1.01  --sat_fm_prep                           false
% 1.94/1.01  --sat_fm_uc_incr                        true
% 1.94/1.01  --sat_out_model                         small
% 1.94/1.01  --sat_out_clauses                       false
% 1.94/1.01  
% 1.94/1.01  ------ QBF Options
% 1.94/1.01  
% 1.94/1.01  --qbf_mode                              false
% 1.94/1.01  --qbf_elim_univ                         false
% 1.94/1.01  --qbf_dom_inst                          none
% 1.94/1.01  --qbf_dom_pre_inst                      false
% 1.94/1.01  --qbf_sk_in                             false
% 1.94/1.01  --qbf_pred_elim                         true
% 1.94/1.01  --qbf_split                             512
% 1.94/1.01  
% 1.94/1.01  ------ BMC1 Options
% 1.94/1.01  
% 1.94/1.01  --bmc1_incremental                      false
% 1.94/1.01  --bmc1_axioms                           reachable_all
% 1.94/1.01  --bmc1_min_bound                        0
% 1.94/1.01  --bmc1_max_bound                        -1
% 1.94/1.01  --bmc1_max_bound_default                -1
% 1.94/1.01  --bmc1_symbol_reachability              true
% 1.94/1.01  --bmc1_property_lemmas                  false
% 1.94/1.01  --bmc1_k_induction                      false
% 1.94/1.01  --bmc1_non_equiv_states                 false
% 1.94/1.01  --bmc1_deadlock                         false
% 1.94/1.01  --bmc1_ucm                              false
% 1.94/1.01  --bmc1_add_unsat_core                   none
% 1.94/1.01  --bmc1_unsat_core_children              false
% 1.94/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/1.01  --bmc1_out_stat                         full
% 1.94/1.01  --bmc1_ground_init                      false
% 1.94/1.01  --bmc1_pre_inst_next_state              false
% 1.94/1.01  --bmc1_pre_inst_state                   false
% 1.94/1.01  --bmc1_pre_inst_reach_state             false
% 1.94/1.01  --bmc1_out_unsat_core                   false
% 1.94/1.01  --bmc1_aig_witness_out                  false
% 1.94/1.01  --bmc1_verbose                          false
% 1.94/1.01  --bmc1_dump_clauses_tptp                false
% 1.94/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.94/1.01  --bmc1_dump_file                        -
% 1.94/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.94/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.94/1.01  --bmc1_ucm_extend_mode                  1
% 1.94/1.01  --bmc1_ucm_init_mode                    2
% 1.94/1.01  --bmc1_ucm_cone_mode                    none
% 1.94/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.94/1.01  --bmc1_ucm_relax_model                  4
% 1.94/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.94/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/1.01  --bmc1_ucm_layered_model                none
% 1.94/1.01  --bmc1_ucm_max_lemma_size               10
% 1.94/1.01  
% 1.94/1.01  ------ AIG Options
% 1.94/1.01  
% 1.94/1.01  --aig_mode                              false
% 1.94/1.01  
% 1.94/1.01  ------ Instantiation Options
% 1.94/1.01  
% 1.94/1.01  --instantiation_flag                    true
% 1.94/1.01  --inst_sos_flag                         false
% 1.94/1.01  --inst_sos_phase                        true
% 1.94/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/1.01  --inst_lit_sel_side                     none
% 1.94/1.01  --inst_solver_per_active                1400
% 1.94/1.01  --inst_solver_calls_frac                1.
% 1.94/1.01  --inst_passive_queue_type               priority_queues
% 1.94/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/1.01  --inst_passive_queues_freq              [25;2]
% 1.94/1.01  --inst_dismatching                      true
% 1.94/1.01  --inst_eager_unprocessed_to_passive     true
% 1.94/1.01  --inst_prop_sim_given                   true
% 1.94/1.01  --inst_prop_sim_new                     false
% 1.94/1.01  --inst_subs_new                         false
% 1.94/1.01  --inst_eq_res_simp                      false
% 1.94/1.01  --inst_subs_given                       false
% 1.94/1.01  --inst_orphan_elimination               true
% 1.94/1.01  --inst_learning_loop_flag               true
% 1.94/1.01  --inst_learning_start                   3000
% 1.94/1.01  --inst_learning_factor                  2
% 1.94/1.01  --inst_start_prop_sim_after_learn       3
% 1.94/1.01  --inst_sel_renew                        solver
% 1.94/1.01  --inst_lit_activity_flag                true
% 1.94/1.01  --inst_restr_to_given                   false
% 1.94/1.01  --inst_activity_threshold               500
% 1.94/1.01  --inst_out_proof                        true
% 1.94/1.01  
% 1.94/1.01  ------ Resolution Options
% 1.94/1.01  
% 1.94/1.01  --resolution_flag                       false
% 1.94/1.01  --res_lit_sel                           adaptive
% 1.94/1.01  --res_lit_sel_side                      none
% 1.94/1.01  --res_ordering                          kbo
% 1.94/1.01  --res_to_prop_solver                    active
% 1.94/1.01  --res_prop_simpl_new                    false
% 1.94/1.01  --res_prop_simpl_given                  true
% 1.94/1.01  --res_passive_queue_type                priority_queues
% 1.94/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/1.01  --res_passive_queues_freq               [15;5]
% 1.94/1.01  --res_forward_subs                      full
% 1.94/1.01  --res_backward_subs                     full
% 1.94/1.01  --res_forward_subs_resolution           true
% 1.94/1.01  --res_backward_subs_resolution          true
% 1.94/1.01  --res_orphan_elimination                true
% 1.94/1.01  --res_time_limit                        2.
% 1.94/1.01  --res_out_proof                         true
% 1.94/1.01  
% 1.94/1.01  ------ Superposition Options
% 1.94/1.01  
% 1.94/1.01  --superposition_flag                    true
% 1.94/1.01  --sup_passive_queue_type                priority_queues
% 1.94/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.94/1.01  --demod_completeness_check              fast
% 1.94/1.01  --demod_use_ground                      true
% 1.94/1.01  --sup_to_prop_solver                    passive
% 1.94/1.01  --sup_prop_simpl_new                    true
% 1.94/1.01  --sup_prop_simpl_given                  true
% 1.94/1.01  --sup_fun_splitting                     false
% 1.94/1.01  --sup_smt_interval                      50000
% 1.94/1.01  
% 1.94/1.01  ------ Superposition Simplification Setup
% 1.94/1.01  
% 1.94/1.01  --sup_indices_passive                   []
% 1.94/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_full_bw                           [BwDemod]
% 1.94/1.01  --sup_immed_triv                        [TrivRules]
% 1.94/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_immed_bw_main                     []
% 1.94/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.01  
% 1.94/1.01  ------ Combination Options
% 1.94/1.01  
% 1.94/1.01  --comb_res_mult                         3
% 1.94/1.01  --comb_sup_mult                         2
% 1.94/1.01  --comb_inst_mult                        10
% 1.94/1.01  
% 1.94/1.01  ------ Debug Options
% 1.94/1.01  
% 1.94/1.01  --dbg_backtrace                         false
% 1.94/1.01  --dbg_dump_prop_clauses                 false
% 1.94/1.01  --dbg_dump_prop_clauses_file            -
% 1.94/1.01  --dbg_out_stat                          false
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  ------ Proving...
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  % SZS status Theorem for theBenchmark.p
% 1.94/1.01  
% 1.94/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.94/1.01  
% 1.94/1.01  fof(f14,conjecture,(
% 1.94/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f15,negated_conjecture,(
% 1.94/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.94/1.01    inference(negated_conjecture,[],[f14])).
% 1.94/1.01  
% 1.94/1.01  fof(f37,plain,(
% 1.94/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f15])).
% 1.94/1.01  
% 1.94/1.01  fof(f38,plain,(
% 1.94/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f37])).
% 1.94/1.01  
% 1.94/1.01  fof(f48,plain,(
% 1.94/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK4) & m1_subset_1(sK4,u1_struct_0(X2)))) )),
% 1.94/1.01    introduced(choice_axiom,[])).
% 1.94/1.01  
% 1.94/1.01  fof(f47,plain,(
% 1.94/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK3,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),X3) & m1_subset_1(X3,u1_struct_0(sK3))) & r1_xboole_0(u1_struct_0(sK3),X1) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.94/1.01    introduced(choice_axiom,[])).
% 1.94/1.01  
% 1.94/1.01  fof(f46,plain,(
% 1.94/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,sK2),k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.94/1.01    introduced(choice_axiom,[])).
% 1.94/1.01  
% 1.94/1.01  fof(f45,plain,(
% 1.94/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK1,X1),k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.94/1.01    introduced(choice_axiom,[])).
% 1.94/1.01  
% 1.94/1.01  fof(f49,plain,(
% 1.94/1.01    (((~r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & r1_xboole_0(u1_struct_0(sK3),sK2) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.94/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f48,f47,f46,f45])).
% 1.94/1.01  
% 1.94/1.01  fof(f76,plain,(
% 1.94/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f11,axiom,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f16,plain,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.94/1.01    inference(pure_predicate_removal,[],[f11])).
% 1.94/1.01  
% 1.94/1.01  fof(f31,plain,(
% 1.94/1.01    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f16])).
% 1.94/1.01  
% 1.94/1.01  fof(f32,plain,(
% 1.94/1.01    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f31])).
% 1.94/1.01  
% 1.94/1.01  fof(f69,plain,(
% 1.94/1.01    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f32])).
% 1.94/1.01  
% 1.94/1.01  fof(f80,plain,(
% 1.94/1.01    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f4,axiom,(
% 1.94/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f19,plain,(
% 1.94/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.94/1.01    inference(ennf_transformation,[],[f4])).
% 1.94/1.01  
% 1.94/1.01  fof(f20,plain,(
% 1.94/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.94/1.01    inference(flattening,[],[f19])).
% 1.94/1.01  
% 1.94/1.01  fof(f59,plain,(
% 1.94/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f20])).
% 1.94/1.01  
% 1.94/1.01  fof(f75,plain,(
% 1.94/1.01    l1_pre_topc(sK1)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f77,plain,(
% 1.94/1.01    ~v2_struct_0(sK3)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f6,axiom,(
% 1.94/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f22,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.94/1.01    inference(ennf_transformation,[],[f6])).
% 1.94/1.01  
% 1.94/1.01  fof(f61,plain,(
% 1.94/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f22])).
% 1.94/1.01  
% 1.94/1.01  fof(f78,plain,(
% 1.94/1.01    m1_pre_topc(sK3,sK1)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f5,axiom,(
% 1.94/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f21,plain,(
% 1.94/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.94/1.01    inference(ennf_transformation,[],[f5])).
% 1.94/1.01  
% 1.94/1.01  fof(f60,plain,(
% 1.94/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f21])).
% 1.94/1.01  
% 1.94/1.01  fof(f7,axiom,(
% 1.94/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f23,plain,(
% 1.94/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f7])).
% 1.94/1.01  
% 1.94/1.01  fof(f24,plain,(
% 1.94/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f23])).
% 1.94/1.01  
% 1.94/1.01  fof(f62,plain,(
% 1.94/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f24])).
% 1.94/1.01  
% 1.94/1.01  fof(f79,plain,(
% 1.94/1.01    r1_xboole_0(u1_struct_0(sK3),sK2)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f3,axiom,(
% 1.94/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f44,plain,(
% 1.94/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.94/1.01    inference(nnf_transformation,[],[f3])).
% 1.94/1.01  
% 1.94/1.01  fof(f57,plain,(
% 1.94/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f44])).
% 1.94/1.01  
% 1.94/1.01  fof(f1,axiom,(
% 1.94/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f39,plain,(
% 1.94/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/1.01    inference(nnf_transformation,[],[f1])).
% 1.94/1.01  
% 1.94/1.01  fof(f40,plain,(
% 1.94/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/1.01    inference(flattening,[],[f39])).
% 1.94/1.01  
% 1.94/1.01  fof(f41,plain,(
% 1.94/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/1.01    inference(rectify,[],[f40])).
% 1.94/1.01  
% 1.94/1.01  fof(f42,plain,(
% 1.94/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.94/1.01    introduced(choice_axiom,[])).
% 1.94/1.01  
% 1.94/1.01  fof(f43,plain,(
% 1.94/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.94/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 1.94/1.01  
% 1.94/1.01  fof(f51,plain,(
% 1.94/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/1.01    inference(cnf_transformation,[],[f43])).
% 1.94/1.01  
% 1.94/1.01  fof(f83,plain,(
% 1.94/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.94/1.01    inference(equality_resolution,[],[f51])).
% 1.94/1.01  
% 1.94/1.01  fof(f12,axiom,(
% 1.94/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f33,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f12])).
% 1.94/1.01  
% 1.94/1.01  fof(f34,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f33])).
% 1.94/1.01  
% 1.94/1.01  fof(f71,plain,(
% 1.94/1.01    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f34])).
% 1.94/1.01  
% 1.94/1.01  fof(f13,axiom,(
% 1.94/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f35,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f13])).
% 1.94/1.01  
% 1.94/1.01  fof(f36,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f35])).
% 1.94/1.01  
% 1.94/1.01  fof(f72,plain,(
% 1.94/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f36])).
% 1.94/1.01  
% 1.94/1.01  fof(f85,plain,(
% 1.94/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(equality_resolution,[],[f72])).
% 1.94/1.01  
% 1.94/1.01  fof(f73,plain,(
% 1.94/1.01    ~v2_struct_0(sK1)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f74,plain,(
% 1.94/1.01    v2_pre_topc(sK1)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f8,axiom,(
% 1.94/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f25,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f8])).
% 1.94/1.01  
% 1.94/1.01  fof(f26,plain,(
% 1.94/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f25])).
% 1.94/1.01  
% 1.94/1.01  fof(f63,plain,(
% 1.94/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f26])).
% 1.94/1.01  
% 1.94/1.01  fof(f81,plain,(
% 1.94/1.01    ~r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)),
% 1.94/1.01    inference(cnf_transformation,[],[f49])).
% 1.94/1.01  
% 1.94/1.01  fof(f9,axiom,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f17,plain,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.94/1.01    inference(pure_predicate_removal,[],[f9])).
% 1.94/1.01  
% 1.94/1.01  fof(f27,plain,(
% 1.94/1.01    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f17])).
% 1.94/1.01  
% 1.94/1.01  fof(f28,plain,(
% 1.94/1.01    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f27])).
% 1.94/1.01  
% 1.94/1.01  fof(f65,plain,(
% 1.94/1.01    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f28])).
% 1.94/1.01  
% 1.94/1.01  fof(f10,axiom,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.94/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.94/1.01  
% 1.94/1.01  fof(f29,plain,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.01    inference(ennf_transformation,[],[f10])).
% 1.94/1.01  
% 1.94/1.01  fof(f30,plain,(
% 1.94/1.01    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.01    inference(flattening,[],[f29])).
% 1.94/1.01  
% 1.94/1.01  fof(f66,plain,(
% 1.94/1.01    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f30])).
% 1.94/1.01  
% 1.94/1.01  fof(f70,plain,(
% 1.94/1.01    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f32])).
% 1.94/1.01  
% 1.94/1.01  fof(f68,plain,(
% 1.94/1.01    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f30])).
% 1.94/1.01  
% 1.94/1.01  fof(f67,plain,(
% 1.94/1.01    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.01    inference(cnf_transformation,[],[f30])).
% 1.94/1.01  
% 1.94/1.01  cnf(c_28,negated_conjecture,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.94/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1909,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_20,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 1.94/1.01      | ~ l1_pre_topc(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1915,plain,
% 1.94/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 1.94/1.01      | v2_pre_topc(X1) != iProver_top
% 1.94/1.01      | v2_struct_0(X1) = iProver_top
% 1.94/1.01      | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
% 1.94/1.01      | l1_pre_topc(X1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3638,plain,
% 1.94/1.01      ( v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(k6_tmap_1(sK1,sK2)) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_1909,c_1915]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_24,negated_conjecture,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.94/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1912,plain,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_9,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1921,plain,
% 1.94/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 1.94/1.01      | r2_hidden(X0,X1) = iProver_top
% 1.94/1.01      | v1_xboole_0(X1) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2923,plain,
% 1.94/1.01      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 1.94/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_1912,c_1921]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_29,negated_conjecture,
% 1.94/1.01      ( l1_pre_topc(sK1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_34,plain,
% 1.94/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_27,negated_conjecture,
% 1.94/1.01      ( ~ v2_struct_0(sK3) ),
% 1.94/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_36,plain,
% 1.94/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_39,plain,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_11,plain,
% 1.94/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_26,negated_conjecture,
% 1.94/1.01      ( m1_pre_topc(sK3,sK1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_594,plain,
% 1.94/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_595,plain,
% 1.94/1.01      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_594]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_596,plain,
% 1.94/1.01      ( l1_pre_topc(sK1) != iProver_top
% 1.94/1.01      | l1_pre_topc(sK3) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2182,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.94/1.01      | r2_hidden(sK4,u1_struct_0(sK3))
% 1.94/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2183,plain,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.94/1.01      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 1.94/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_10,plain,
% 1.94/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_12,plain,
% 1.94/1.01      ( v2_struct_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.94/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_409,plain,
% 1.94/1.01      ( v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X0)
% 1.94/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.94/1.01      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2239,plain,
% 1.94/1.01      ( v2_struct_0(sK3)
% 1.94/1.01      | ~ l1_pre_topc(sK3)
% 1.94/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_409]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2240,plain,
% 1.94/1.01      ( v2_struct_0(sK3) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK3) != iProver_top
% 1.94/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3279,plain,
% 1.94/1.01      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_2923,c_34,c_36,c_39,c_596,c_2183,c_2240]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_25,negated_conjecture,
% 1.94/1.01      ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
% 1.94/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1911,plain,
% 1.94/1.01      ( r1_xboole_0(u1_struct_0(sK3),sK2) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_8,plain,
% 1.94/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 1.94/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1922,plain,
% 1.94/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2262,plain,
% 1.94/1.01      ( k4_xboole_0(u1_struct_0(sK3),sK2) = u1_struct_0(sK3) ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_1911,c_1922]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_4,plain,
% 1.94/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 1.94/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1926,plain,
% 1.94/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.94/1.01      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2861,plain,
% 1.94/1.01      ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 1.94/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_2262,c_1926]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3397,plain,
% 1.94/1.01      ( r2_hidden(sK4,sK2) != iProver_top ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_3279,c_2861]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_21,plain,
% 1.94/1.01      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.01      | r2_hidden(X2,X1)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2234,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK4)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 1.94/1.01      | r2_hidden(sK4,X0)
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3259,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
% 1.94/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | r2_hidden(sK4,sK2)
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_2234]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3260,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) = iProver_top
% 1.94/1.01      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | r2_hidden(sK4,sK2) = iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_3259]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_22,plain,
% 1.94/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.94/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.94/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.94/1.01      | ~ m1_pre_topc(X4,X0)
% 1.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.94/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.94/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.94/1.01      | ~ v1_funct_1(X2)
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X4)
% 1.94/1.01      | ~ l1_pre_topc(X1)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f85]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_605,plain,
% 1.94/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.94/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.94/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.94/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.94/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.94/1.01      | ~ v1_funct_1(X2)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v2_struct_0(X4)
% 1.94/1.01      | ~ l1_pre_topc(X0)
% 1.94/1.01      | ~ l1_pre_topc(X1)
% 1.94/1.01      | sK1 != X0
% 1.94/1.01      | sK3 != X4 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_606,plain,
% 1.94/1.01      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.94/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.94/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.94/1.01      | ~ v1_funct_1(X1)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | v2_struct_0(sK3)
% 1.94/1.01      | ~ l1_pre_topc(X0)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_605]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_31,negated_conjecture,
% 1.94/1.01      ( ~ v2_struct_0(sK1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_30,negated_conjecture,
% 1.94/1.01      ( v2_pre_topc(sK1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_610,plain,
% 1.94/1.01      ( ~ l1_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.94/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.94/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.94/1.01      | ~ v1_funct_1(X1)
% 1.94/1.01      | ~ v2_pre_topc(X0) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_606,c_31,c_30,c_29,c_27]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_611,plain,
% 1.94/1.01      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.94/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.94/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.94/1.01      | ~ v1_funct_1(X1)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_610]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_13,plain,
% 1.94/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_576,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.94/1.01      | m1_subset_1(X0,u1_struct_0(X2))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v2_struct_0(X2)
% 1.94/1.01      | ~ l1_pre_topc(X2)
% 1.94/1.01      | sK1 != X2
% 1.94/1.01      | sK3 != X1 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_577,plain,
% 1.94/1.01      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | v2_struct_0(sK3)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_576]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_581,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.94/1.01      | m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_577,c_31,c_29,c_27]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_582,plain,
% 1.94/1.01      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_581]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_626,plain,
% 1.94/1.01      ( ~ r1_tmap_1(sK1,X0,X1,X2)
% 1.94/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2)
% 1.94/1.01      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.94/1.01      | ~ v1_funct_1(X1)
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(forward_subsumption_resolution,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_611,c_582]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1902,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,X0,X1,X2) != iProver_top
% 1.94/1.01      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,X1,sK3),X2) = iProver_top
% 1.94/1.01      | v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top
% 1.94/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
% 1.94/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.94/1.01      | v1_funct_1(X1) != iProver_top
% 1.94/1.01      | v2_pre_topc(X0) != iProver_top
% 1.94/1.01      | v2_struct_0(X0) = iProver_top
% 1.94/1.01      | l1_pre_topc(X0) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_23,negated_conjecture,
% 1.94/1.01      ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
% 1.94/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1913,plain,
% 1.94/1.01      ( r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2257,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top
% 1.94/1.01      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 1.94/1.01      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.94/1.01      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 1.94/1.01      | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 1.94/1.01      | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
% 1.94/1.01      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 1.94/1.01      inference(superposition,[status(thm)],[c_1902,c_1913]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_32,plain,
% 1.94/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_33,plain,
% 1.94/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_35,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_14,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X1)
% 1.94/1.01      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 1.94/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2188,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | l1_pre_topc(k6_tmap_1(sK1,sK2))
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2189,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_18,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | v1_funct_1(k7_tmap_1(X1,X0))
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2191,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | v1_funct_1(k7_tmap_1(sK1,sK2))
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2192,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2191]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_19,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_pre_topc(k6_tmap_1(X1,X0))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2194,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | v2_pre_topc(k6_tmap_1(sK1,sK2))
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2195,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | v2_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_16,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 1.94/1.01      | ~ v2_pre_topc(X1)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X1) ),
% 1.94/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2211,plain,
% 1.94/1.01      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2212,plain,
% 1.94/1.01      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2211]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_17,plain,
% 1.94/1.01      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2214,plain,
% 1.94/1.01      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ v2_pre_topc(sK1)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2215,plain,
% 1.94/1.01      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.94/1.01      | v2_struct_0(sK1) = iProver_top
% 1.94/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2782,plain,
% 1.94/1.01      ( v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top
% 1.94/1.01      | r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_2257,c_32,c_33,c_34,c_35,c_39,c_2189,c_2192,c_2195,
% 1.94/1.01                 c_2212,c_2215]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2783,plain,
% 1.94/1.01      ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4) != iProver_top
% 1.94/1.01      | v2_struct_0(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_2782]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2171,plain,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1))
% 1.94/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_582]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2172,plain,
% 1.94/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top
% 1.94/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(contradiction,plain,
% 1.94/1.01      ( $false ),
% 1.94/1.01      inference(minisat,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_3638,c_3397,c_3260,c_2783,c_2172,c_39,c_35,c_34,c_33,
% 1.94/1.01                 c_32]) ).
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.94/1.01  
% 1.94/1.01  ------                               Statistics
% 1.94/1.01  
% 1.94/1.01  ------ General
% 1.94/1.01  
% 1.94/1.01  abstr_ref_over_cycles:                  0
% 1.94/1.01  abstr_ref_under_cycles:                 0
% 1.94/1.01  gc_basic_clause_elim:                   0
% 1.94/1.01  forced_gc_time:                         0
% 1.94/1.01  parsing_time:                           0.012
% 1.94/1.01  unif_index_cands_time:                  0.
% 1.94/1.01  unif_index_add_time:                    0.
% 1.94/1.01  orderings_time:                         0.
% 1.94/1.01  out_proof_time:                         0.011
% 1.94/1.01  total_time:                             0.165
% 1.94/1.01  num_of_symbols:                         55
% 1.94/1.01  num_of_terms:                           2862
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing
% 1.94/1.01  
% 1.94/1.01  num_of_splits:                          0
% 1.94/1.01  num_of_split_atoms:                     0
% 1.94/1.01  num_of_reused_defs:                     0
% 1.94/1.01  num_eq_ax_congr_red:                    16
% 1.94/1.01  num_of_sem_filtered_clauses:            1
% 1.94/1.01  num_of_subtypes:                        0
% 1.94/1.01  monotx_restored_types:                  0
% 1.94/1.01  sat_num_of_epr_types:                   0
% 1.94/1.01  sat_num_of_non_cyclic_types:            0
% 1.94/1.01  sat_guarded_non_collapsed_types:        0
% 1.94/1.01  num_pure_diseq_elim:                    0
% 1.94/1.01  simp_replaced_by:                       0
% 1.94/1.01  res_preprocessed:                       155
% 1.94/1.01  prep_upred:                             0
% 1.94/1.01  prep_unflattend:                        14
% 1.94/1.01  smt_new_axioms:                         0
% 1.94/1.01  pred_elim_cands:                        10
% 1.94/1.01  pred_elim:                              2
% 1.94/1.01  pred_elim_cl:                           2
% 1.94/1.01  pred_elim_cycles:                       10
% 1.94/1.01  merged_defs:                            8
% 1.94/1.01  merged_defs_ncl:                        0
% 1.94/1.01  bin_hyper_res:                          8
% 1.94/1.01  prep_cycles:                            4
% 1.94/1.01  pred_elim_time:                         0.022
% 1.94/1.01  splitting_time:                         0.
% 1.94/1.01  sem_filter_time:                        0.
% 1.94/1.01  monotx_time:                            0.001
% 1.94/1.01  subtype_inf_time:                       0.
% 1.94/1.01  
% 1.94/1.01  ------ Problem properties
% 1.94/1.01  
% 1.94/1.01  clauses:                                29
% 1.94/1.01  conjectures:                            8
% 1.94/1.01  epr:                                    7
% 1.94/1.01  horn:                                   17
% 1.94/1.01  ground:                                 9
% 1.94/1.01  unary:                                  9
% 1.94/1.01  binary:                                 6
% 1.94/1.01  lits:                                   86
% 1.94/1.01  lits_eq:                                5
% 1.94/1.01  fd_pure:                                0
% 1.94/1.01  fd_pseudo:                              0
% 1.94/1.01  fd_cond:                                0
% 1.94/1.01  fd_pseudo_cond:                         3
% 1.94/1.01  ac_symbols:                             0
% 1.94/1.01  
% 1.94/1.01  ------ Propositional Solver
% 1.94/1.01  
% 1.94/1.01  prop_solver_calls:                      26
% 1.94/1.01  prop_fast_solver_calls:                 1194
% 1.94/1.01  smt_solver_calls:                       0
% 1.94/1.01  smt_fast_solver_calls:                  0
% 1.94/1.01  prop_num_of_clauses:                    929
% 1.94/1.01  prop_preprocess_simplified:             5029
% 1.94/1.01  prop_fo_subsumed:                       17
% 1.94/1.01  prop_solver_time:                       0.
% 1.94/1.01  smt_solver_time:                        0.
% 1.94/1.01  smt_fast_solver_time:                   0.
% 1.94/1.01  prop_fast_solver_time:                  0.
% 1.94/1.01  prop_unsat_core_time:                   0.
% 1.94/1.01  
% 1.94/1.01  ------ QBF
% 1.94/1.01  
% 1.94/1.01  qbf_q_res:                              0
% 1.94/1.01  qbf_num_tautologies:                    0
% 1.94/1.01  qbf_prep_cycles:                        0
% 1.94/1.01  
% 1.94/1.01  ------ BMC1
% 1.94/1.01  
% 1.94/1.01  bmc1_current_bound:                     -1
% 1.94/1.01  bmc1_last_solved_bound:                 -1
% 1.94/1.01  bmc1_unsat_core_size:                   -1
% 1.94/1.01  bmc1_unsat_core_parents_size:           -1
% 1.94/1.01  bmc1_merge_next_fun:                    0
% 1.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.94/1.01  
% 1.94/1.01  ------ Instantiation
% 1.94/1.01  
% 1.94/1.01  inst_num_of_clauses:                    264
% 1.94/1.01  inst_num_in_passive:                    59
% 1.94/1.01  inst_num_in_active:                     147
% 1.94/1.01  inst_num_in_unprocessed:                58
% 1.94/1.01  inst_num_of_loops:                      170
% 1.94/1.01  inst_num_of_learning_restarts:          0
% 1.94/1.01  inst_num_moves_active_passive:          20
% 1.94/1.01  inst_lit_activity:                      0
% 1.94/1.01  inst_lit_activity_moves:                0
% 1.94/1.01  inst_num_tautologies:                   0
% 1.94/1.01  inst_num_prop_implied:                  0
% 1.94/1.01  inst_num_existing_simplified:           0
% 1.94/1.01  inst_num_eq_res_simplified:             0
% 1.94/1.01  inst_num_child_elim:                    0
% 1.94/1.01  inst_num_of_dismatching_blockings:      46
% 1.94/1.01  inst_num_of_non_proper_insts:           175
% 1.94/1.01  inst_num_of_duplicates:                 0
% 1.94/1.01  inst_inst_num_from_inst_to_res:         0
% 1.94/1.01  inst_dismatching_checking_time:         0.
% 1.94/1.01  
% 1.94/1.01  ------ Resolution
% 1.94/1.01  
% 1.94/1.01  res_num_of_clauses:                     0
% 1.94/1.01  res_num_in_passive:                     0
% 1.94/1.01  res_num_in_active:                      0
% 1.94/1.01  res_num_of_loops:                       159
% 1.94/1.01  res_forward_subset_subsumed:            13
% 1.94/1.01  res_backward_subset_subsumed:           0
% 1.94/1.01  res_forward_subsumed:                   0
% 1.94/1.01  res_backward_subsumed:                  0
% 1.94/1.01  res_forward_subsumption_resolution:     5
% 1.94/1.01  res_backward_subsumption_resolution:    0
% 1.94/1.01  res_clause_to_clause_subsumption:       146
% 1.94/1.01  res_orphan_elimination:                 0
% 1.94/1.01  res_tautology_del:                      43
% 1.94/1.01  res_num_eq_res_simplified:              0
% 1.94/1.01  res_num_sel_changes:                    0
% 1.94/1.01  res_moves_from_active_to_pass:          0
% 1.94/1.01  
% 1.94/1.01  ------ Superposition
% 1.94/1.01  
% 1.94/1.01  sup_time_total:                         0.
% 1.94/1.01  sup_time_generating:                    0.
% 1.94/1.01  sup_time_sim_full:                      0.
% 1.94/1.01  sup_time_sim_immed:                     0.
% 1.94/1.01  
% 1.94/1.01  sup_num_of_clauses:                     49
% 1.94/1.01  sup_num_in_active:                      34
% 1.94/1.01  sup_num_in_passive:                     15
% 1.94/1.01  sup_num_of_loops:                       33
% 1.94/1.01  sup_fw_superposition:                   19
% 1.94/1.01  sup_bw_superposition:                   13
% 1.94/1.01  sup_immediate_simplified:               3
% 1.94/1.01  sup_given_eliminated:                   0
% 1.94/1.01  comparisons_done:                       0
% 1.94/1.01  comparisons_avoided:                    0
% 1.94/1.01  
% 1.94/1.01  ------ Simplifications
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  sim_fw_subset_subsumed:                 0
% 1.94/1.01  sim_bw_subset_subsumed:                 0
% 1.94/1.01  sim_fw_subsumed:                        3
% 1.94/1.01  sim_bw_subsumed:                        0
% 1.94/1.01  sim_fw_subsumption_res:                 0
% 1.94/1.01  sim_bw_subsumption_res:                 0
% 1.94/1.01  sim_tautology_del:                      6
% 1.94/1.01  sim_eq_tautology_del:                   0
% 1.94/1.01  sim_eq_res_simp:                        1
% 1.94/1.01  sim_fw_demodulated:                     0
% 1.94/1.01  sim_bw_demodulated:                     0
% 1.94/1.01  sim_light_normalised:                   0
% 1.94/1.01  sim_joinable_taut:                      0
% 1.94/1.01  sim_joinable_simp:                      0
% 1.94/1.01  sim_ac_normalised:                      0
% 1.94/1.01  sim_smt_subsumption:                    0
% 1.94/1.01  
%------------------------------------------------------------------------------
