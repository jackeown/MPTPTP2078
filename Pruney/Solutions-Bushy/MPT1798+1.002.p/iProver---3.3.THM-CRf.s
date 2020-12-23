%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1798+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:27 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  146 (3709 expanded)
%              Number of clauses        :   97 ( 851 expanded)
%              Number of leaves         :   12 (1189 expanded)
%              Depth                    :   24
%              Number of atoms          :  651 (27219 expanded)
%              Number of equality atoms :  230 (9429 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( u1_struct_0(X1) = X2
                   => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
              & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,sK3)
        & u1_struct_0(X1) = sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ? [X2] :
              ( u1_pre_topc(k8_tmap_1(X0,sK2)) != k5_tmap_1(X0,X2)
              & u1_struct_0(sK2) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(sK1,X1)) != k5_tmap_1(sK1,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
            | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(sK1,sK3)
        & u1_struct_0(sK2) = sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,sK2)) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f30,f29,f28])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
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
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,
    ( u1_struct_0(sK2) = sK3
    | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_267,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_268,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_270,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_18])).

cnf(c_1660,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_19,c_18])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_629])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_19,c_18])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_19,c_18,c_661])).

cnf(c_1636,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_2470,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))),u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2)))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1660,c_1636])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_19,c_18])).

cnf(c_1648,plain,
    ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,X0)) = k6_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_2204,plain,
    ( g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,u1_struct_0(sK2))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1660,c_1648])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1665,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2668,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = X0
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_1665])).

cnf(c_23,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_269,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k5_tmap_1(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k5_tmap_1(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_19,c_18])).

cnf(c_1949,plain,
    ( m1_subset_1(k5_tmap_1(sK1,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_1950,plain,
    ( m1_subset_1(k5_tmap_1(sK1,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_2669,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = X0
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X1,X0)
    | m1_subset_1(k5_tmap_1(sK1,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_1665])).

cnf(c_3101,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X1,X0)
    | k5_tmap_1(sK1,u1_struct_0(sK2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2668,c_23,c_269,c_1950,c_2669])).

cnf(c_3102,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = X0
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X1,X0) ),
    inference(renaming,[status(thm)],[c_3101])).

cnf(c_3107,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_2470,c_3102])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1664,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2666,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_1664])).

cnf(c_2667,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(k5_tmap_1(sK1,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_1664])).

cnf(c_3000,plain,
    ( u1_struct_0(sK1) = X0
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2666,c_23,c_269,c_1950,c_2667])).

cnf(c_3001,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(renaming,[status(thm)],[c_3000])).

cnf(c_3006,plain,
    ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2470,c_3001])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_220,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_221,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_225,plain,
    ( ~ l1_pre_topc(X0)
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_221,c_20,c_19,c_18])).

cnf(c_226,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK2,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | k8_tmap_1(sK1,sK2) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_629])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK2,k6_tmap_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK2,k6_tmap_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_902,c_19,c_18,c_643,c_661])).

cnf(c_1637,plain,
    ( k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k6_tmap_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_3319,plain,
    ( k6_tmap_1(sK1,X0) = k8_tmap_1(sK1,sK2)
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0)))) = k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1648])).

cnf(c_3823,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2)
    | g1_pre_topc(u1_struct_0(sK1),k5_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,u1_struct_0(sK2))))) = k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,u1_struct_0(sK2)))) ),
    inference(superposition,[status(thm)],[c_1660,c_3319])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_278,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X1)
    | sK0(X0,X2,X1) = u1_struct_0(X2)
    | k8_tmap_1(X0,X2) = X1
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_279,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_283,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_20,c_19,c_18])).

cnf(c_284,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_880,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(sK1,sK2,X1) = u1_struct_0(sK2)
    | k6_tmap_1(sK1,X0) != X1
    | k8_tmap_1(sK1,sK2) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_629])).

cnf(c_881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_885,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_19,c_18,c_643,c_661])).

cnf(c_1638,plain,
    ( sK0(sK1,sK2,k6_tmap_1(sK1,X0)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_3226,plain,
    ( sK0(sK1,sK2,k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1660,c_1638])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_305,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X1)
    | k6_tmap_1(X0,sK0(X0,X2,X1)) != X1
    | k8_tmap_1(X0,X2) = X1
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_306,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_20,c_19,c_18])).

cnf(c_311,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | k6_tmap_1(sK1,sK0(sK1,sK2,X1)) != X1
    | k8_tmap_1(sK1,sK2) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_311,c_629])).

cnf(c_860,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0))) != k6_tmap_1(sK1,X0)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0))) != k6_tmap_1(sK1,X0)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_19,c_18,c_643,c_661])).

cnf(c_1639,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0))) != k6_tmap_1(sK1,X0)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_3229,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_1639])).

cnf(c_3901,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3823,c_23,c_269,c_3229])).

cnf(c_4168,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_3006,c_3901])).

cnf(c_14,negated_conjecture,
    ( u1_struct_0(sK2) = sK3
    | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4172,plain,
    ( u1_struct_0(sK2) = sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_4168,c_14])).

cnf(c_4173,plain,
    ( u1_struct_0(sK2) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_4172])).

cnf(c_4185,plain,
    ( k6_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4173,c_3901])).

cnf(c_4855,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = k5_tmap_1(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3107,c_4173,c_4185])).

cnf(c_13,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4171,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_4168,c_13])).

cnf(c_4176,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_4171])).

cnf(c_4857,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4855,c_4176])).


%------------------------------------------------------------------------------
