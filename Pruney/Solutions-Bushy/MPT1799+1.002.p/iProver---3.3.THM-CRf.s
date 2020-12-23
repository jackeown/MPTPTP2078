%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1799+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  131 (2062 expanded)
%              Number of clauses        :   86 ( 489 expanded)
%              Number of leaves         :   10 ( 654 expanded)
%              Depth                    :   26
%              Number of atoms          :  656 (15614 expanded)
%              Number of equality atoms :  165 (2311 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                    & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
            | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
          & u1_struct_0(X1) = u1_struct_0(X2)
          & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
     => ( ( ~ m1_pre_topc(sK3,k8_tmap_1(X0,X1))
          | ~ v1_tsep_1(sK3,k8_tmap_1(X0,X1)) )
        & u1_struct_0(sK3) = u1_struct_0(X1)
        & m1_pre_topc(sK3,k8_tmap_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,sK2))
              | ~ v1_tsep_1(X2,k8_tmap_1(X0,sK2)) )
            & u1_struct_0(sK2) = u1_struct_0(X2)
            & m1_pre_topc(X2,k8_tmap_1(X0,sK2)) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
                & u1_struct_0(X1) = u1_struct_0(X2)
                & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(sK1,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(sK1,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(sK1,X1)) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
      | ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) )
    & u1_struct_0(sK2) = u1_struct_0(sK3)
    & m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f27,f26,f25])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f48,plain,
    ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    | ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_656,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_657,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_659,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_17])).

cnf(c_2521,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_3388,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2521])).

cnf(c_13,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2525,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3448,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3388,c_2525])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_667,plain,
    ( v2_struct_0(X0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X0,X2,X1) = u1_struct_0(X2)
    | k8_tmap_1(X0,X2) = X1
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_668,plain,
    ( v2_struct_0(sK1)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_672,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_19,c_18,c_17])).

cnf(c_673,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1213])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1214,c_18,c_17])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(sK1,sK2,X1) = u1_struct_0(sK2)
    | k6_tmap_1(sK1,X0) != X1
    | k8_tmap_1(sK1,sK2) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_673,c_1218])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_2095])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1231])).

cnf(c_1236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1232,c_18,c_17])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_1250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1249])).

cnf(c_1254,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1250,c_18,c_17])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_1254])).

cnf(c_2100,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2096,c_18,c_17,c_1232,c_1250])).

cnf(c_2498,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0_44)
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2100])).

cnf(c_3428,plain,
    ( k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0_44)
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK2)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_3582,plain,
    ( k6_tmap_1(sK1,X0_44) = k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2,k6_tmap_1(sK1,X0_44)) = u1_struct_0(sK3)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3428,c_2525])).

cnf(c_4033,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2,k6_tmap_1(sK1,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3448,c_3582])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_694,plain,
    ( v2_struct_0(X0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,sK0(X0,X2,X1)) != X1
    | k8_tmap_1(X0,X2) = X1
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_695,plain,
    ( v2_struct_0(sK1)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_19,c_18,c_17])).

cnf(c_700,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_2074,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | k6_tmap_1(sK1,sK0(sK1,sK2,X1)) != X1
    | k8_tmap_1(sK1,sK2) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_700,c_1218])).

cnf(c_2075,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0))) != k6_tmap_1(sK1,X0)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_2074])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0))) != k6_tmap_1(sK1,X0)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2075,c_18,c_17,c_1232,c_1250])).

cnf(c_2499,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0_44))) != k6_tmap_1(sK1,X0_44)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0_44) ),
    inference(subtyping,[status(esa)],[c_2079])).

cnf(c_3427,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK2,k6_tmap_1(sK1,X0_44))) != k6_tmap_1(sK1,X0_44)
    | k8_tmap_1(sK1,sK2) = k6_tmap_1(sK1,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2499])).

cnf(c_5066,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4033,c_3427])).

cnf(c_5128,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5066,c_3448])).

cnf(c_2515,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_1255])).

cnf(c_3396,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2515])).

cnf(c_4461,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3448,c_3396])).

cnf(c_5131,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5128,c_4461])).

cnf(c_7,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_119,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_120,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_12,negated_conjecture,
    ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2))
    | ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_106,negated_conjecture,
    ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_227,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_120,c_106])).

cnf(c_228,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
    | ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_230,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_14])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_230])).

cnf(c_249,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,u1_struct_0(sK3)))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_1136,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,u1_struct_0(sK3)))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_249,c_19])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1136])).

cnf(c_251,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1139,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1137,c_19,c_18,c_17,c_251])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_1139])).

cnf(c_2519,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_1140])).

cnf(c_3390,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_3781,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK3))))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3390,c_3448])).

cnf(c_5132,plain,
    ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5128,c_3781])).

cnf(c_5136,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5132])).

cnf(c_2516,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_1236])).

cnf(c_3395,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

cnf(c_4288,plain,
    ( v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3448,c_3395])).

cnf(c_5133,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5128,c_4288])).

cnf(c_5140,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5136,c_5133])).

cnf(c_5145,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5131,c_5140])).

cnf(c_566,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_567,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_568,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5145,c_5131,c_568])).


%------------------------------------------------------------------------------
