%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:07 EST 2020

% Result     : CounterSatisfiable 2.70s
% Output     : Saturation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  402 (4354 expanded)
%              Number of clauses        :  314 ( 898 expanded)
%              Number of leaves         :   35 (1607 expanded)
%              Depth                    :   25
%              Number of atoms          : 1841 (35371 expanded)
%              Number of equality atoms :  576 (1309 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK4)
        & m1_subset_1(sK4,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK3,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3),X3)
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & r1_tsep_1(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK2,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f52,f51,f50,f49])).

fof(f84,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ~ r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f47])).

cnf(c_4311,plain,
    ( k5_tmap_1(X0_60,X0_59) = k5_tmap_1(X1_60,X1_59)
    | X0_60 != X1_60
    | X0_59 != X1_59 ),
    theory(equality)).

cnf(c_4310,plain,
    ( u1_pre_topc(X0_60) = u1_pre_topc(X1_60)
    | X0_60 != X1_60 ),
    theory(equality)).

cnf(c_4295,plain,
    ( X0_62 != X1_62
    | X2_62 != X1_62
    | X2_62 = X0_62 ),
    theory(equality)).

cnf(c_4291,plain,
    ( X0_62 = X0_62 ),
    theory(equality)).

cnf(c_20,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_23,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_194,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23])).

cnf(c_195,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1501,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_27])).

cnf(c_1502,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1504,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_33,c_32,c_31,c_28])).

cnf(c_4279,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_1504])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1645,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_29])).

cnf(c_1646,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1645])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1648,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1646,c_33,c_32,c_31,c_30])).

cnf(c_4274,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1648])).

cnf(c_352,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_349,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_347,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_342,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_341,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_337,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_336,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_335,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_333,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_332,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4287,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1394,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_1395,plain,
    ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1394])).

cnf(c_1399,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_33,c_32,c_31])).

cnf(c_1400,plain,
    ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1399])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1683,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_1684,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1683])).

cnf(c_1686,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1684,c_33,c_32,c_31])).

cnf(c_2232,plain,
    ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1400,c_1686])).

cnf(c_2233,plain,
    ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_2232])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1694,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_1695,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1694])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1705,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_1706,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1705])).

cnf(c_2235,plain,
    ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_33,c_32,c_31,c_1695,c_1706])).

cnf(c_4261,plain,
    ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_2235])).

cnf(c_4738,plain,
    ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
    | m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4261])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_33])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1997])).

cnf(c_2002,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1998,c_32,c_31])).

cnf(c_4268,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_59) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_2002])).

cnf(c_4735,plain,
    ( k7_tmap_1(sK1,X0_59) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4268])).

cnf(c_5954,plain,
    ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
    | k7_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4738,c_4735])).

cnf(c_1653,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_1654,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1653])).

cnf(c_1656,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_31])).

cnf(c_4273,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_1656])).

cnf(c_4731,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4273])).

cnf(c_5324,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4731,c_4735])).

cnf(c_11,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_389,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(X2,X1) != k8_tmap_1(sK1,sK2)
    | sK4 != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_390,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_394,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(sK3,X1)
    | ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_28,c_25])).

cnf(c_395,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1781,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2)
    | sK1 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_395])).

cnf(c_1782,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1781])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_33,c_32,c_31])).

cnf(c_1787,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_1786])).

cnf(c_2085,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,X2),k7_tmap_1(sK1,X2),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,X2) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != X2
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_1787])).

cnf(c_2086,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X1)),k7_tmap_1(sK1,u1_struct_0(X1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(X1)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2085])).

cnf(c_4267,plain,
    ( ~ r1_tsep_1(X0_60,X1_60)
    | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X1_60)),k7_tmap_1(sK1,u1_struct_0(X1_60)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(X1_60)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2086])).

cnf(c_4736,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X0_60)),k7_tmap_1(sK1,u1_struct_0(X0_60)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(X0_60)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X1_60) != u1_struct_0(sK3)
    | r1_tsep_1(X1_60,X0_60) != iProver_top
    | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X1_60) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4267])).

cnf(c_5836,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5324,c_4736])).

cnf(c_9,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_211,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_23,c_14,c_13,c_12])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_1637,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_29])).

cnf(c_1638,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1637])).

cnf(c_1640,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_33,c_32,c_31])).

cnf(c_4275,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_1640])).

cnf(c_5837,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5836,c_4275])).

cnf(c_5838,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5837])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1655,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1770,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_1771,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1770])).

cnf(c_1773,plain,
    ( l1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_31])).

cnf(c_2288,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1773])).

cnf(c_2289,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2288])).

cnf(c_2290,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2289])).

cnf(c_5875,plain,
    ( l1_struct_0(X0_60) != iProver_top
    | k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5838,c_36,c_1655,c_2290])).

cnf(c_5876,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK2) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(renaming,[status(thm)],[c_5875])).

cnf(c_1466,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_1467,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_1466])).

cnf(c_1471,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_33,c_32,c_31])).

cnf(c_1472,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_1471])).

cnf(c_1539,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_1540,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1539])).

cnf(c_1542,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_33,c_32,c_31])).

cnf(c_2188,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) = X0
    | k8_tmap_1(sK1,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1472,c_1542])).

cnf(c_2189,plain,
    ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_2188])).

cnf(c_1550,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_1551,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1550])).

cnf(c_1561,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_1562,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1561])).

cnf(c_2191,plain,
    ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_33,c_32,c_31,c_1551,c_1562])).

cnf(c_4264,plain,
    ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_2191])).

cnf(c_4737,plain,
    ( k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3)
    | m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4264])).

cnf(c_5825,plain,
    ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
    | k7_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4737,c_4735])).

cnf(c_1509,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_1510,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1509])).

cnf(c_1512,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_31])).

cnf(c_4278,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_1512])).

cnf(c_4729,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4278])).

cnf(c_5323,plain,
    ( k7_tmap_1(sK1,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4729,c_4735])).

cnf(c_1493,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_27])).

cnf(c_1494,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_1493])).

cnf(c_1496,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_33,c_32,c_31])).

cnf(c_4280,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_1496])).

cnf(c_5419,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4280,c_4736])).

cnf(c_5477,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5419,c_4280])).

cnf(c_1511,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_1626,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_1627,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1626])).

cnf(c_1629,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_31])).

cnf(c_2274,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1629])).

cnf(c_2275,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2274])).

cnf(c_2276,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_5616,plain,
    ( l1_struct_0(X0_60) != iProver_top
    | k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5477,c_36,c_1511,c_2276])).

cnf(c_5617,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK3) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(renaming,[status(thm)],[c_5616])).

cnf(c_5749,plain,
    ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,sK3) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5323,c_5617])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1520,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_1521,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1520])).

cnf(c_1523,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_33,c_32,c_31,c_28])).

cnf(c_4277,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1523])).

cnf(c_5423,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_4736])).

cnf(c_5447,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5423,c_4277])).

cnf(c_1564,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1562,c_33,c_32,c_31])).

cnf(c_2267,plain,
    ( l1_struct_0(X0)
    | k8_tmap_1(sK1,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1564])).

cnf(c_2268,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_2267])).

cnf(c_2269,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_5689,plain,
    ( l1_struct_0(X0_60) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5447,c_2269])).

cnf(c_5690,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(renaming,[status(thm)],[c_5689])).

cnf(c_1664,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_1665,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1664])).

cnf(c_1667,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1665,c_33,c_32,c_31,c_30])).

cnf(c_4272,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1667])).

cnf(c_5424,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4272,c_4736])).

cnf(c_5432,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5424,c_4272])).

cnf(c_1708,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_33,c_32,c_31])).

cnf(c_2281,plain,
    ( l1_struct_0(X0)
    | k8_tmap_1(sK1,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1708])).

cnf(c_2282,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_2281])).

cnf(c_2283,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_5676,plain,
    ( l1_struct_0(X0_60) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5432,c_2283])).

cnf(c_5677,plain,
    ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
    | u1_struct_0(X0_60) != u1_struct_0(sK3)
    | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top ),
    inference(renaming,[status(thm)],[c_5676])).

cnf(c_26,negated_conjecture,
    ( r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4284,negated_conjecture,
    ( r1_tsep_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_4725,plain,
    ( r1_tsep_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4284])).

cnf(c_18,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4286,plain,
    ( ~ r1_tsep_1(X0_60,X1_60)
    | r1_tsep_1(X1_60,X0_60)
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_4723,plain,
    ( r1_tsep_1(X0_60,X1_60) != iProver_top
    | r1_tsep_1(X1_60,X0_60) = iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4286])).

cnf(c_4993,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_4723])).

cnf(c_41,plain,
    ( r1_tsep_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4947,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4286])).

cnf(c_4948,plain,
    ( r1_tsep_1(sK2,sK3) != iProver_top
    | r1_tsep_1(sK3,sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4947])).

cnf(c_5027,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4993,c_41,c_2276,c_2290,c_4948])).

cnf(c_15,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1455,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_1456,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1455])).

cnf(c_1458,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1456,c_33,c_32,c_31])).

cnf(c_4281,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_1458])).

cnf(c_4728,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4281])).

cnf(c_4785,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4728,c_4272])).

cnf(c_1383,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_1384,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3)))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1383])).

cnf(c_1386,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1384,c_33,c_32,c_31])).

cnf(c_4282,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) ),
    inference(subtyping,[status(esa)],[c_1386])).

cnf(c_4727,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4282])).

cnf(c_4782,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4727,c_4277])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_pre_topc(X6,X7)
    | ~ v2_pre_topc(X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_477,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_16,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_481,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k3_struct_0(X0))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_16,c_15,c_2,c_0])).

cnf(c_482,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_481])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_509,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_482,c_17])).

cnf(c_1421,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_509,c_29])).

cnf(c_1422,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ l1_pre_topc(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1424,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_33,c_32,c_31,c_30])).

cnf(c_1425,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1424])).

cnf(c_1924,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_1425])).

cnf(c_110,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1926,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1924])).

cnf(c_1928,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1924,c_33,c_32,c_31,c_30,c_110,c_1665,c_1926])).

cnf(c_1929,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1928])).

cnf(c_1372,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_1373,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1372])).

cnf(c_1375,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1373,c_33,c_32,c_31])).

cnf(c_2026,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1929,c_1375])).

cnf(c_2028,plain,
    ( k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2026,c_33,c_32,c_31,c_28,c_1521])).

cnf(c_2029,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_2028])).

cnf(c_1528,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_1529,plain,
    ( ~ v2_pre_topc(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1528])).

cnf(c_1531,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_33,c_32,c_31])).

cnf(c_2121,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_2029,c_1531])).

cnf(c_3264,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_2121])).

cnf(c_4254,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_3264])).

cnf(c_4745,plain,
    ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4254])).

cnf(c_1349,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_509,c_27])).

cnf(c_1350,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1349])).

cnf(c_1352,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1350,c_33,c_32,c_31,c_28])).

cnf(c_1353,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1352])).

cnf(c_1903,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_1353])).

cnf(c_1905,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_1907,plain,
    ( k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1903,c_33,c_32,c_31,c_28,c_110,c_1521,c_1905])).

cnf(c_1908,plain,
    ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1907])).

cnf(c_1444,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_1445,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_1447,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_33,c_32,c_31])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1908,c_1447])).

cnf(c_2052,plain,
    ( k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | ~ v1_funct_1(k3_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_33,c_32,c_31,c_30,c_1665])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_2052])).

cnf(c_1672,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_1673,plain,
    ( ~ v2_pre_topc(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1672])).

cnf(c_1675,plain,
    ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1673,c_33,c_32,c_31])).

cnf(c_2136,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_2053,c_1675])).

cnf(c_3262,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_2136])).

cnf(c_4255,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_3262])).

cnf(c_4744,plain,
    ( k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
    | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
    | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4255])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_30])).

cnf(c_1977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1976])).

cnf(c_1981,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1977,c_31,c_1771])).

cnf(c_1982,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_1981])).

cnf(c_4269,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1982])).

cnf(c_4734,plain,
    ( k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4269])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_1956,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1955])).

cnf(c_1960,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_31,c_1627])).

cnf(c_1961,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1960])).

cnf(c_4270,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1961])).

cnf(c_4733,plain,
    ( k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4270])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1743,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_1744,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_1743])).

cnf(c_1748,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1744,c_33,c_32,c_31])).

cnf(c_1749,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_1748])).

cnf(c_2162,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
    | k8_tmap_1(sK1,sK2) = X0
    | k8_tmap_1(sK1,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1749,c_1542])).

cnf(c_2163,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
    | k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_2162])).

cnf(c_2165,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2163,c_33,c_32,c_31,c_1551,c_1562])).

cnf(c_4266,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_2165])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1716,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_1717,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_1716])).

cnf(c_1721,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_33,c_32,c_31])).

cnf(c_1722,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_1721])).

cnf(c_2173,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = X0
    | k8_tmap_1(sK1,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1722,c_1542])).

cnf(c_2174,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
    | sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_2173])).

cnf(c_2176,plain,
    ( sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2)
    | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_33,c_32,c_31,c_1551,c_1562])).

cnf(c_4265,plain,
    ( k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3)
    | sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2176])).

cnf(c_1599,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_1600,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1599])).

cnf(c_1604,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1600,c_33,c_32,c_31])).

cnf(c_1605,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1604])).

cnf(c_2208,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
    | k8_tmap_1(sK1,sK2) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1605,c_1686])).

cnf(c_2209,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_2208])).

cnf(c_2211,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2209,c_33,c_32,c_31,c_1695,c_1706])).

cnf(c_4263,plain,
    ( k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_2211])).

cnf(c_1572,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_1573,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1572])).

cnf(c_1577,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1573,c_33,c_32,c_31])).

cnf(c_1578,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1577])).

cnf(c_2219,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK2) != X0
    | k8_tmap_1(sK1,sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1578,c_1686])).

cnf(c_2220,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_2219])).

cnf(c_2222,plain,
    ( sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3)
    | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2220,c_33,c_32,c_31,c_1695,c_1706])).

cnf(c_4262,plain,
    ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2222])).

cnf(c_4256,plain,
    ( l1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2289])).

cnf(c_4743,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4256])).

cnf(c_4257,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_2282])).

cnf(c_4742,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4257])).

cnf(c_4258,plain,
    ( l1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2275])).

cnf(c_4741,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4258])).

cnf(c_4259,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_2268])).

cnf(c_4740,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4259])).

cnf(c_2260,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_31])).

cnf(c_2261,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_2260])).

cnf(c_4260,plain,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_2261])).

cnf(c_4739,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4260])).

cnf(c_1697,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_33,c_32,c_31])).

cnf(c_4271,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1697])).

cnf(c_4732,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4271])).

cnf(c_1553,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1551,c_33,c_32,c_31])).

cnf(c_4276,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_1553])).

cnf(c_4730,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4276])).

cnf(c_4285,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_4724,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4285])).

cnf(c_4283,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_4726,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:26:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.70/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.01  
% 2.70/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.01  
% 2.70/1.01  ------  iProver source info
% 2.70/1.01  
% 2.70/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.01  git: non_committed_changes: false
% 2.70/1.01  git: last_make_outside_of_git: false
% 2.70/1.01  
% 2.70/1.01  ------ 
% 2.70/1.01  
% 2.70/1.01  ------ Input Options
% 2.70/1.01  
% 2.70/1.01  --out_options                           all
% 2.70/1.01  --tptp_safe_out                         true
% 2.70/1.01  --problem_path                          ""
% 2.70/1.01  --include_path                          ""
% 2.70/1.01  --clausifier                            res/vclausify_rel
% 2.70/1.01  --clausifier_options                    --mode clausify
% 2.70/1.01  --stdin                                 false
% 2.70/1.01  --stats_out                             all
% 2.70/1.01  
% 2.70/1.01  ------ General Options
% 2.70/1.01  
% 2.70/1.01  --fof                                   false
% 2.70/1.01  --time_out_real                         305.
% 2.70/1.01  --time_out_virtual                      -1.
% 2.70/1.01  --symbol_type_check                     false
% 2.70/1.01  --clausify_out                          false
% 2.70/1.01  --sig_cnt_out                           false
% 2.70/1.01  --trig_cnt_out                          false
% 2.70/1.01  --trig_cnt_out_tolerance                1.
% 2.70/1.01  --trig_cnt_out_sk_spl                   false
% 2.70/1.01  --abstr_cl_out                          false
% 2.70/1.01  
% 2.70/1.01  ------ Global Options
% 2.70/1.01  
% 2.70/1.01  --schedule                              default
% 2.70/1.01  --add_important_lit                     false
% 2.70/1.01  --prop_solver_per_cl                    1000
% 2.70/1.01  --min_unsat_core                        false
% 2.70/1.01  --soft_assumptions                      false
% 2.70/1.01  --soft_lemma_size                       3
% 2.70/1.01  --prop_impl_unit_size                   0
% 2.70/1.01  --prop_impl_unit                        []
% 2.70/1.01  --share_sel_clauses                     true
% 2.70/1.01  --reset_solvers                         false
% 2.70/1.01  --bc_imp_inh                            [conj_cone]
% 2.70/1.01  --conj_cone_tolerance                   3.
% 2.70/1.01  --extra_neg_conj                        none
% 2.70/1.01  --large_theory_mode                     true
% 2.70/1.01  --prolific_symb_bound                   200
% 2.70/1.01  --lt_threshold                          2000
% 2.70/1.01  --clause_weak_htbl                      true
% 2.70/1.01  --gc_record_bc_elim                     false
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing Options
% 2.70/1.01  
% 2.70/1.01  --preprocessing_flag                    true
% 2.70/1.01  --time_out_prep_mult                    0.1
% 2.70/1.01  --splitting_mode                        input
% 2.70/1.01  --splitting_grd                         true
% 2.70/1.01  --splitting_cvd                         false
% 2.70/1.01  --splitting_cvd_svl                     false
% 2.70/1.01  --splitting_nvd                         32
% 2.70/1.01  --sub_typing                            true
% 2.70/1.01  --prep_gs_sim                           true
% 2.70/1.01  --prep_unflatten                        true
% 2.70/1.01  --prep_res_sim                          true
% 2.70/1.01  --prep_upred                            true
% 2.70/1.01  --prep_sem_filter                       exhaustive
% 2.70/1.01  --prep_sem_filter_out                   false
% 2.70/1.01  --pred_elim                             true
% 2.70/1.01  --res_sim_input                         true
% 2.70/1.01  --eq_ax_congr_red                       true
% 2.70/1.01  --pure_diseq_elim                       true
% 2.70/1.01  --brand_transform                       false
% 2.70/1.01  --non_eq_to_eq                          false
% 2.70/1.01  --prep_def_merge                        true
% 2.70/1.01  --prep_def_merge_prop_impl              false
% 2.70/1.01  --prep_def_merge_mbd                    true
% 2.70/1.01  --prep_def_merge_tr_red                 false
% 2.70/1.01  --prep_def_merge_tr_cl                  false
% 2.70/1.01  --smt_preprocessing                     true
% 2.70/1.01  --smt_ac_axioms                         fast
% 2.70/1.01  --preprocessed_out                      false
% 2.70/1.01  --preprocessed_stats                    false
% 2.70/1.01  
% 2.70/1.01  ------ Abstraction refinement Options
% 2.70/1.01  
% 2.70/1.01  --abstr_ref                             []
% 2.70/1.01  --abstr_ref_prep                        false
% 2.70/1.01  --abstr_ref_until_sat                   false
% 2.70/1.01  --abstr_ref_sig_restrict                funpre
% 2.70/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.01  --abstr_ref_under                       []
% 2.70/1.01  
% 2.70/1.01  ------ SAT Options
% 2.70/1.01  
% 2.70/1.01  --sat_mode                              false
% 2.70/1.01  --sat_fm_restart_options                ""
% 2.70/1.01  --sat_gr_def                            false
% 2.70/1.01  --sat_epr_types                         true
% 2.70/1.01  --sat_non_cyclic_types                  false
% 2.70/1.01  --sat_finite_models                     false
% 2.70/1.01  --sat_fm_lemmas                         false
% 2.70/1.01  --sat_fm_prep                           false
% 2.70/1.01  --sat_fm_uc_incr                        true
% 2.70/1.01  --sat_out_model                         small
% 2.70/1.01  --sat_out_clauses                       false
% 2.70/1.01  
% 2.70/1.01  ------ QBF Options
% 2.70/1.01  
% 2.70/1.01  --qbf_mode                              false
% 2.70/1.01  --qbf_elim_univ                         false
% 2.70/1.01  --qbf_dom_inst                          none
% 2.70/1.01  --qbf_dom_pre_inst                      false
% 2.70/1.01  --qbf_sk_in                             false
% 2.70/1.01  --qbf_pred_elim                         true
% 2.70/1.01  --qbf_split                             512
% 2.70/1.01  
% 2.70/1.01  ------ BMC1 Options
% 2.70/1.01  
% 2.70/1.01  --bmc1_incremental                      false
% 2.70/1.01  --bmc1_axioms                           reachable_all
% 2.70/1.01  --bmc1_min_bound                        0
% 2.70/1.01  --bmc1_max_bound                        -1
% 2.70/1.01  --bmc1_max_bound_default                -1
% 2.70/1.01  --bmc1_symbol_reachability              true
% 2.70/1.01  --bmc1_property_lemmas                  false
% 2.70/1.01  --bmc1_k_induction                      false
% 2.70/1.01  --bmc1_non_equiv_states                 false
% 2.70/1.01  --bmc1_deadlock                         false
% 2.70/1.01  --bmc1_ucm                              false
% 2.70/1.01  --bmc1_add_unsat_core                   none
% 2.70/1.01  --bmc1_unsat_core_children              false
% 2.70/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.01  --bmc1_out_stat                         full
% 2.70/1.01  --bmc1_ground_init                      false
% 2.70/1.01  --bmc1_pre_inst_next_state              false
% 2.70/1.01  --bmc1_pre_inst_state                   false
% 2.70/1.01  --bmc1_pre_inst_reach_state             false
% 2.70/1.01  --bmc1_out_unsat_core                   false
% 2.70/1.01  --bmc1_aig_witness_out                  false
% 2.70/1.01  --bmc1_verbose                          false
% 2.70/1.01  --bmc1_dump_clauses_tptp                false
% 2.70/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.01  --bmc1_dump_file                        -
% 2.70/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.01  --bmc1_ucm_extend_mode                  1
% 2.70/1.01  --bmc1_ucm_init_mode                    2
% 2.70/1.01  --bmc1_ucm_cone_mode                    none
% 2.70/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.01  --bmc1_ucm_relax_model                  4
% 2.70/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.01  --bmc1_ucm_layered_model                none
% 2.70/1.01  --bmc1_ucm_max_lemma_size               10
% 2.70/1.01  
% 2.70/1.01  ------ AIG Options
% 2.70/1.01  
% 2.70/1.01  --aig_mode                              false
% 2.70/1.01  
% 2.70/1.01  ------ Instantiation Options
% 2.70/1.01  
% 2.70/1.01  --instantiation_flag                    true
% 2.70/1.01  --inst_sos_flag                         false
% 2.70/1.01  --inst_sos_phase                        true
% 2.70/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.01  --inst_lit_sel_side                     num_symb
% 2.70/1.01  --inst_solver_per_active                1400
% 2.70/1.01  --inst_solver_calls_frac                1.
% 2.70/1.01  --inst_passive_queue_type               priority_queues
% 2.70/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.01  --inst_passive_queues_freq              [25;2]
% 2.70/1.01  --inst_dismatching                      true
% 2.70/1.01  --inst_eager_unprocessed_to_passive     true
% 2.70/1.01  --inst_prop_sim_given                   true
% 2.70/1.01  --inst_prop_sim_new                     false
% 2.70/1.01  --inst_subs_new                         false
% 2.70/1.01  --inst_eq_res_simp                      false
% 2.70/1.01  --inst_subs_given                       false
% 2.70/1.01  --inst_orphan_elimination               true
% 2.70/1.01  --inst_learning_loop_flag               true
% 2.70/1.01  --inst_learning_start                   3000
% 2.70/1.01  --inst_learning_factor                  2
% 2.70/1.01  --inst_start_prop_sim_after_learn       3
% 2.70/1.01  --inst_sel_renew                        solver
% 2.70/1.01  --inst_lit_activity_flag                true
% 2.70/1.01  --inst_restr_to_given                   false
% 2.70/1.01  --inst_activity_threshold               500
% 2.70/1.01  --inst_out_proof                        true
% 2.70/1.01  
% 2.70/1.01  ------ Resolution Options
% 2.70/1.01  
% 2.70/1.01  --resolution_flag                       true
% 2.70/1.01  --res_lit_sel                           adaptive
% 2.70/1.01  --res_lit_sel_side                      none
% 2.70/1.01  --res_ordering                          kbo
% 2.70/1.01  --res_to_prop_solver                    active
% 2.70/1.01  --res_prop_simpl_new                    false
% 2.70/1.01  --res_prop_simpl_given                  true
% 2.70/1.01  --res_passive_queue_type                priority_queues
% 2.70/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.01  --res_passive_queues_freq               [15;5]
% 2.70/1.01  --res_forward_subs                      full
% 2.70/1.01  --res_backward_subs                     full
% 2.70/1.01  --res_forward_subs_resolution           true
% 2.70/1.01  --res_backward_subs_resolution          true
% 2.70/1.01  --res_orphan_elimination                true
% 2.70/1.01  --res_time_limit                        2.
% 2.70/1.01  --res_out_proof                         true
% 2.70/1.01  
% 2.70/1.01  ------ Superposition Options
% 2.70/1.01  
% 2.70/1.01  --superposition_flag                    true
% 2.70/1.01  --sup_passive_queue_type                priority_queues
% 2.70/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.01  --demod_completeness_check              fast
% 2.70/1.01  --demod_use_ground                      true
% 2.70/1.01  --sup_to_prop_solver                    passive
% 2.70/1.01  --sup_prop_simpl_new                    true
% 2.70/1.01  --sup_prop_simpl_given                  true
% 2.70/1.01  --sup_fun_splitting                     false
% 2.70/1.01  --sup_smt_interval                      50000
% 2.70/1.01  
% 2.70/1.01  ------ Superposition Simplification Setup
% 2.70/1.01  
% 2.70/1.01  --sup_indices_passive                   []
% 2.70/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_full_bw                           [BwDemod]
% 2.70/1.01  --sup_immed_triv                        [TrivRules]
% 2.70/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_immed_bw_main                     []
% 2.70/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.01  
% 2.70/1.01  ------ Combination Options
% 2.70/1.01  
% 2.70/1.01  --comb_res_mult                         3
% 2.70/1.01  --comb_sup_mult                         2
% 2.70/1.01  --comb_inst_mult                        10
% 2.70/1.01  
% 2.70/1.01  ------ Debug Options
% 2.70/1.01  
% 2.70/1.01  --dbg_backtrace                         false
% 2.70/1.01  --dbg_dump_prop_clauses                 false
% 2.70/1.01  --dbg_dump_prop_clauses_file            -
% 2.70/1.01  --dbg_out_stat                          false
% 2.70/1.01  ------ Parsing...
% 2.70/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.01  ------ Proving...
% 2.70/1.01  ------ Problem Properties 
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  clauses                                 33
% 2.70/1.01  conjectures                             3
% 2.70/1.01  EPR                                     6
% 2.70/1.01  Horn                                    29
% 2.70/1.01  unary                                   20
% 2.70/1.01  binary                                  7
% 2.70/1.01  lits                                    57
% 2.70/1.01  lits eq                                 26
% 2.70/1.01  fd_pure                                 0
% 2.70/1.01  fd_pseudo                               0
% 2.70/1.01  fd_cond                                 0
% 2.70/1.01  fd_pseudo_cond                          0
% 2.70/1.01  AC symbols                              0
% 2.70/1.01  
% 2.70/1.01  ------ Schedule dynamic 5 is on 
% 2.70/1.01  
% 2.70/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  ------ 
% 2.70/1.01  Current options:
% 2.70/1.01  ------ 
% 2.70/1.01  
% 2.70/1.01  ------ Input Options
% 2.70/1.01  
% 2.70/1.01  --out_options                           all
% 2.70/1.01  --tptp_safe_out                         true
% 2.70/1.01  --problem_path                          ""
% 2.70/1.01  --include_path                          ""
% 2.70/1.01  --clausifier                            res/vclausify_rel
% 2.70/1.01  --clausifier_options                    --mode clausify
% 2.70/1.01  --stdin                                 false
% 2.70/1.01  --stats_out                             all
% 2.70/1.01  
% 2.70/1.01  ------ General Options
% 2.70/1.01  
% 2.70/1.01  --fof                                   false
% 2.70/1.01  --time_out_real                         305.
% 2.70/1.01  --time_out_virtual                      -1.
% 2.70/1.01  --symbol_type_check                     false
% 2.70/1.01  --clausify_out                          false
% 2.70/1.01  --sig_cnt_out                           false
% 2.70/1.01  --trig_cnt_out                          false
% 2.70/1.01  --trig_cnt_out_tolerance                1.
% 2.70/1.01  --trig_cnt_out_sk_spl                   false
% 2.70/1.01  --abstr_cl_out                          false
% 2.70/1.01  
% 2.70/1.01  ------ Global Options
% 2.70/1.01  
% 2.70/1.01  --schedule                              default
% 2.70/1.01  --add_important_lit                     false
% 2.70/1.01  --prop_solver_per_cl                    1000
% 2.70/1.01  --min_unsat_core                        false
% 2.70/1.01  --soft_assumptions                      false
% 2.70/1.01  --soft_lemma_size                       3
% 2.70/1.01  --prop_impl_unit_size                   0
% 2.70/1.01  --prop_impl_unit                        []
% 2.70/1.01  --share_sel_clauses                     true
% 2.70/1.01  --reset_solvers                         false
% 2.70/1.01  --bc_imp_inh                            [conj_cone]
% 2.70/1.01  --conj_cone_tolerance                   3.
% 2.70/1.01  --extra_neg_conj                        none
% 2.70/1.01  --large_theory_mode                     true
% 2.70/1.01  --prolific_symb_bound                   200
% 2.70/1.01  --lt_threshold                          2000
% 2.70/1.01  --clause_weak_htbl                      true
% 2.70/1.01  --gc_record_bc_elim                     false
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing Options
% 2.70/1.01  
% 2.70/1.01  --preprocessing_flag                    true
% 2.70/1.01  --time_out_prep_mult                    0.1
% 2.70/1.01  --splitting_mode                        input
% 2.70/1.01  --splitting_grd                         true
% 2.70/1.01  --splitting_cvd                         false
% 2.70/1.01  --splitting_cvd_svl                     false
% 2.70/1.01  --splitting_nvd                         32
% 2.70/1.01  --sub_typing                            true
% 2.70/1.01  --prep_gs_sim                           true
% 2.70/1.01  --prep_unflatten                        true
% 2.70/1.01  --prep_res_sim                          true
% 2.70/1.01  --prep_upred                            true
% 2.70/1.01  --prep_sem_filter                       exhaustive
% 2.70/1.01  --prep_sem_filter_out                   false
% 2.70/1.01  --pred_elim                             true
% 2.70/1.01  --res_sim_input                         true
% 2.70/1.01  --eq_ax_congr_red                       true
% 2.70/1.01  --pure_diseq_elim                       true
% 2.70/1.01  --brand_transform                       false
% 2.70/1.01  --non_eq_to_eq                          false
% 2.70/1.01  --prep_def_merge                        true
% 2.70/1.01  --prep_def_merge_prop_impl              false
% 2.70/1.01  --prep_def_merge_mbd                    true
% 2.70/1.01  --prep_def_merge_tr_red                 false
% 2.70/1.01  --prep_def_merge_tr_cl                  false
% 2.70/1.01  --smt_preprocessing                     true
% 2.70/1.01  --smt_ac_axioms                         fast
% 2.70/1.01  --preprocessed_out                      false
% 2.70/1.01  --preprocessed_stats                    false
% 2.70/1.01  
% 2.70/1.01  ------ Abstraction refinement Options
% 2.70/1.01  
% 2.70/1.01  --abstr_ref                             []
% 2.70/1.01  --abstr_ref_prep                        false
% 2.70/1.01  --abstr_ref_until_sat                   false
% 2.70/1.01  --abstr_ref_sig_restrict                funpre
% 2.70/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.01  --abstr_ref_under                       []
% 2.70/1.01  
% 2.70/1.01  ------ SAT Options
% 2.70/1.01  
% 2.70/1.01  --sat_mode                              false
% 2.70/1.01  --sat_fm_restart_options                ""
% 2.70/1.01  --sat_gr_def                            false
% 2.70/1.01  --sat_epr_types                         true
% 2.70/1.01  --sat_non_cyclic_types                  false
% 2.70/1.01  --sat_finite_models                     false
% 2.70/1.01  --sat_fm_lemmas                         false
% 2.70/1.01  --sat_fm_prep                           false
% 2.70/1.01  --sat_fm_uc_incr                        true
% 2.70/1.01  --sat_out_model                         small
% 2.70/1.01  --sat_out_clauses                       false
% 2.70/1.01  
% 2.70/1.01  ------ QBF Options
% 2.70/1.01  
% 2.70/1.01  --qbf_mode                              false
% 2.70/1.01  --qbf_elim_univ                         false
% 2.70/1.01  --qbf_dom_inst                          none
% 2.70/1.01  --qbf_dom_pre_inst                      false
% 2.70/1.01  --qbf_sk_in                             false
% 2.70/1.01  --qbf_pred_elim                         true
% 2.70/1.01  --qbf_split                             512
% 2.70/1.01  
% 2.70/1.01  ------ BMC1 Options
% 2.70/1.01  
% 2.70/1.01  --bmc1_incremental                      false
% 2.70/1.01  --bmc1_axioms                           reachable_all
% 2.70/1.01  --bmc1_min_bound                        0
% 2.70/1.01  --bmc1_max_bound                        -1
% 2.70/1.01  --bmc1_max_bound_default                -1
% 2.70/1.01  --bmc1_symbol_reachability              true
% 2.70/1.01  --bmc1_property_lemmas                  false
% 2.70/1.01  --bmc1_k_induction                      false
% 2.70/1.01  --bmc1_non_equiv_states                 false
% 2.70/1.01  --bmc1_deadlock                         false
% 2.70/1.01  --bmc1_ucm                              false
% 2.70/1.01  --bmc1_add_unsat_core                   none
% 2.70/1.01  --bmc1_unsat_core_children              false
% 2.70/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.01  --bmc1_out_stat                         full
% 2.70/1.01  --bmc1_ground_init                      false
% 2.70/1.01  --bmc1_pre_inst_next_state              false
% 2.70/1.01  --bmc1_pre_inst_state                   false
% 2.70/1.01  --bmc1_pre_inst_reach_state             false
% 2.70/1.01  --bmc1_out_unsat_core                   false
% 2.70/1.01  --bmc1_aig_witness_out                  false
% 2.70/1.01  --bmc1_verbose                          false
% 2.70/1.01  --bmc1_dump_clauses_tptp                false
% 2.70/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.01  --bmc1_dump_file                        -
% 2.70/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.01  --bmc1_ucm_extend_mode                  1
% 2.70/1.01  --bmc1_ucm_init_mode                    2
% 2.70/1.01  --bmc1_ucm_cone_mode                    none
% 2.70/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.01  --bmc1_ucm_relax_model                  4
% 2.70/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.01  --bmc1_ucm_layered_model                none
% 2.70/1.01  --bmc1_ucm_max_lemma_size               10
% 2.70/1.01  
% 2.70/1.01  ------ AIG Options
% 2.70/1.01  
% 2.70/1.01  --aig_mode                              false
% 2.70/1.01  
% 2.70/1.01  ------ Instantiation Options
% 2.70/1.01  
% 2.70/1.01  --instantiation_flag                    true
% 2.70/1.01  --inst_sos_flag                         false
% 2.70/1.01  --inst_sos_phase                        true
% 2.70/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.01  --inst_lit_sel_side                     none
% 2.70/1.01  --inst_solver_per_active                1400
% 2.70/1.01  --inst_solver_calls_frac                1.
% 2.70/1.01  --inst_passive_queue_type               priority_queues
% 2.70/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.01  --inst_passive_queues_freq              [25;2]
% 2.70/1.01  --inst_dismatching                      true
% 2.70/1.01  --inst_eager_unprocessed_to_passive     true
% 2.70/1.01  --inst_prop_sim_given                   true
% 2.70/1.01  --inst_prop_sim_new                     false
% 2.70/1.01  --inst_subs_new                         false
% 2.70/1.01  --inst_eq_res_simp                      false
% 2.70/1.01  --inst_subs_given                       false
% 2.70/1.01  --inst_orphan_elimination               true
% 2.70/1.01  --inst_learning_loop_flag               true
% 2.70/1.01  --inst_learning_start                   3000
% 2.70/1.01  --inst_learning_factor                  2
% 2.70/1.01  --inst_start_prop_sim_after_learn       3
% 2.70/1.01  --inst_sel_renew                        solver
% 2.70/1.01  --inst_lit_activity_flag                true
% 2.70/1.01  --inst_restr_to_given                   false
% 2.70/1.01  --inst_activity_threshold               500
% 2.70/1.01  --inst_out_proof                        true
% 2.70/1.01  
% 2.70/1.01  ------ Resolution Options
% 2.70/1.01  
% 2.70/1.01  --resolution_flag                       false
% 2.70/1.01  --res_lit_sel                           adaptive
% 2.70/1.01  --res_lit_sel_side                      none
% 2.70/1.01  --res_ordering                          kbo
% 2.70/1.01  --res_to_prop_solver                    active
% 2.70/1.01  --res_prop_simpl_new                    false
% 2.70/1.01  --res_prop_simpl_given                  true
% 2.70/1.01  --res_passive_queue_type                priority_queues
% 2.70/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.01  --res_passive_queues_freq               [15;5]
% 2.70/1.01  --res_forward_subs                      full
% 2.70/1.01  --res_backward_subs                     full
% 2.70/1.01  --res_forward_subs_resolution           true
% 2.70/1.01  --res_backward_subs_resolution          true
% 2.70/1.01  --res_orphan_elimination                true
% 2.70/1.01  --res_time_limit                        2.
% 2.70/1.01  --res_out_proof                         true
% 2.70/1.01  
% 2.70/1.01  ------ Superposition Options
% 2.70/1.01  
% 2.70/1.01  --superposition_flag                    true
% 2.70/1.01  --sup_passive_queue_type                priority_queues
% 2.70/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.01  --demod_completeness_check              fast
% 2.70/1.01  --demod_use_ground                      true
% 2.70/1.01  --sup_to_prop_solver                    passive
% 2.70/1.01  --sup_prop_simpl_new                    true
% 2.70/1.01  --sup_prop_simpl_given                  true
% 2.70/1.01  --sup_fun_splitting                     false
% 2.70/1.01  --sup_smt_interval                      50000
% 2.70/1.01  
% 2.70/1.01  ------ Superposition Simplification Setup
% 2.70/1.01  
% 2.70/1.01  --sup_indices_passive                   []
% 2.70/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_full_bw                           [BwDemod]
% 2.70/1.01  --sup_immed_triv                        [TrivRules]
% 2.70/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_immed_bw_main                     []
% 2.70/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.01  
% 2.70/1.01  ------ Combination Options
% 2.70/1.01  
% 2.70/1.01  --comb_res_mult                         3
% 2.70/1.01  --comb_sup_mult                         2
% 2.70/1.01  --comb_inst_mult                        10
% 2.70/1.01  
% 2.70/1.01  ------ Debug Options
% 2.70/1.01  
% 2.70/1.01  --dbg_backtrace                         false
% 2.70/1.01  --dbg_dump_prop_clauses                 false
% 2.70/1.01  --dbg_dump_prop_clauses_file            -
% 2.70/1.01  --dbg_out_stat                          false
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  ------ Proving...
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 2.70/1.01  
% 2.70/1.01  % SZS output start Saturation for theBenchmark.p
% 2.70/1.01  
% 2.70/1.01  fof(f12,axiom,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f36,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f12])).
% 2.70/1.01  
% 2.70/1.01  fof(f37,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f36])).
% 2.70/1.01  
% 2.70/1.01  fof(f75,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f37])).
% 2.70/1.01  
% 2.70/1.01  fof(f91,plain,(
% 2.70/1.01    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(equality_resolution,[],[f75])).
% 2.70/1.01  
% 2.70/1.01  fof(f14,axiom,(
% 2.70/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f40,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.70/1.01    inference(ennf_transformation,[],[f14])).
% 2.70/1.01  
% 2.70/1.01  fof(f77,plain,(
% 2.70/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f40])).
% 2.70/1.01  
% 2.70/1.01  fof(f15,conjecture,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f16,negated_conjecture,(
% 2.70/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 2.70/1.01    inference(negated_conjecture,[],[f15])).
% 2.70/1.01  
% 2.70/1.01  fof(f41,plain,(
% 2.70/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f16])).
% 2.70/1.01  
% 2.70/1.01  fof(f42,plain,(
% 2.70/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f41])).
% 2.70/1.01  
% 2.70/1.01  fof(f52,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK4) & m1_subset_1(sK4,u1_struct_0(X2)))) )),
% 2.70/1.01    introduced(choice_axiom,[])).
% 2.70/1.01  
% 2.70/1.01  fof(f51,plain,(
% 2.70/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK3,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3),X3) & m1_subset_1(X3,u1_struct_0(sK3))) & r1_tsep_1(X1,sK3) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.70/1.01    introduced(choice_axiom,[])).
% 2.70/1.01  
% 2.70/1.01  fof(f50,plain,(
% 2.70/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.70/1.01    introduced(choice_axiom,[])).
% 2.70/1.01  
% 2.70/1.01  fof(f49,plain,(
% 2.70/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK1,X1),k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.70/1.01    introduced(choice_axiom,[])).
% 2.70/1.01  
% 2.70/1.01  fof(f53,plain,(
% 2.70/1.01    (((~r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.70/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f52,f51,f50,f49])).
% 2.70/1.01  
% 2.70/1.01  fof(f84,plain,(
% 2.70/1.01    m1_pre_topc(sK3,sK1)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f78,plain,(
% 2.70/1.01    ~v2_struct_0(sK1)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f79,plain,(
% 2.70/1.01    v2_pre_topc(sK1)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f80,plain,(
% 2.70/1.01    l1_pre_topc(sK1)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f83,plain,(
% 2.70/1.01    ~v2_struct_0(sK3)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f82,plain,(
% 2.70/1.01    m1_pre_topc(sK2,sK1)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f81,plain,(
% 2.70/1.01    ~v2_struct_0(sK2)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f6,axiom,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f25,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f6])).
% 2.70/1.01  
% 2.70/1.01  fof(f26,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f25])).
% 2.70/1.01  
% 2.70/1.01  fof(f44,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(nnf_transformation,[],[f26])).
% 2.70/1.01  
% 2.70/1.01  fof(f45,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(rectify,[],[f44])).
% 2.70/1.01  
% 2.70/1.01  fof(f46,plain,(
% 2.70/1.01    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.01    introduced(choice_axiom,[])).
% 2.70/1.01  
% 2.70/1.01  fof(f47,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 2.70/1.01  
% 2.70/1.01  fof(f61,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f47])).
% 2.70/1.01  
% 2.70/1.01  fof(f8,axiom,(
% 2.70/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f28,plain,(
% 2.70/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f8])).
% 2.70/1.01  
% 2.70/1.01  fof(f29,plain,(
% 2.70/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f28])).
% 2.70/1.01  
% 2.70/1.01  fof(f66,plain,(
% 2.70/1.01    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f29])).
% 2.70/1.01  
% 2.70/1.01  fof(f67,plain,(
% 2.70/1.01    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f29])).
% 2.70/1.01  
% 2.70/1.01  fof(f68,plain,(
% 2.70/1.01    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f29])).
% 2.70/1.01  
% 2.70/1.01  fof(f5,axiom,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f23,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f5])).
% 2.70/1.01  
% 2.70/1.01  fof(f24,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f23])).
% 2.70/1.01  
% 2.70/1.01  fof(f59,plain,(
% 2.70/1.01    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f24])).
% 2.70/1.01  
% 2.70/1.01  fof(f7,axiom,(
% 2.70/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f27,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.70/1.01    inference(ennf_transformation,[],[f7])).
% 2.70/1.01  
% 2.70/1.01  fof(f48,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.70/1.01    inference(nnf_transformation,[],[f27])).
% 2.70/1.01  
% 2.70/1.01  fof(f64,plain,(
% 2.70/1.01    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f48])).
% 2.70/1.01  
% 2.70/1.01  fof(f11,axiom,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f34,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f11])).
% 2.70/1.01  
% 2.70/1.01  fof(f35,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f34])).
% 2.70/1.01  
% 2.70/1.01  fof(f73,plain,(
% 2.70/1.01    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f35])).
% 2.70/1.01  
% 2.70/1.01  fof(f87,plain,(
% 2.70/1.01    ~r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f86,plain,(
% 2.70/1.01    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f60,plain,(
% 2.70/1.01    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f47])).
% 2.70/1.01  
% 2.70/1.01  fof(f89,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(equality_resolution,[],[f60])).
% 2.70/1.01  
% 2.70/1.01  fof(f90,plain,(
% 2.70/1.01    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(equality_resolution,[],[f89])).
% 2.70/1.01  
% 2.70/1.01  fof(f1,axiom,(
% 2.70/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f17,plain,(
% 2.70/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.70/1.01    inference(ennf_transformation,[],[f1])).
% 2.70/1.01  
% 2.70/1.01  fof(f54,plain,(
% 2.70/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f17])).
% 2.70/1.01  
% 2.70/1.01  fof(f2,axiom,(
% 2.70/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f18,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.70/1.01    inference(ennf_transformation,[],[f2])).
% 2.70/1.01  
% 2.70/1.01  fof(f55,plain,(
% 2.70/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f18])).
% 2.70/1.01  
% 2.70/1.01  fof(f74,plain,(
% 2.70/1.01    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f37])).
% 2.70/1.01  
% 2.70/1.01  fof(f85,plain,(
% 2.70/1.01    r1_tsep_1(sK2,sK3)),
% 2.70/1.01    inference(cnf_transformation,[],[f53])).
% 2.70/1.01  
% 2.70/1.01  fof(f10,axiom,(
% 2.70/1.01    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f32,plain,(
% 2.70/1.01    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f10])).
% 2.70/1.01  
% 2.70/1.01  fof(f33,plain,(
% 2.70/1.01    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f32])).
% 2.70/1.01  
% 2.70/1.01  fof(f72,plain,(
% 2.70/1.01    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f33])).
% 2.70/1.01  
% 2.70/1.01  fof(f9,axiom,(
% 2.70/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f30,plain,(
% 2.70/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f9])).
% 2.70/1.01  
% 2.70/1.01  fof(f31,plain,(
% 2.70/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f30])).
% 2.70/1.01  
% 2.70/1.01  fof(f71,plain,(
% 2.70/1.01    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f31])).
% 2.70/1.01  
% 2.70/1.01  fof(f3,axiom,(
% 2.70/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f19,plain,(
% 2.70/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f3])).
% 2.70/1.01  
% 2.70/1.01  fof(f20,plain,(
% 2.70/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f19])).
% 2.70/1.01  
% 2.70/1.01  fof(f56,plain,(
% 2.70/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f20])).
% 2.70/1.01  
% 2.70/1.01  fof(f4,axiom,(
% 2.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f21,plain,(
% 2.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.70/1.01    inference(ennf_transformation,[],[f4])).
% 2.70/1.01  
% 2.70/1.01  fof(f22,plain,(
% 2.70/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.70/1.01    inference(flattening,[],[f21])).
% 2.70/1.01  
% 2.70/1.01  fof(f43,plain,(
% 2.70/1.01    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.70/1.01    inference(nnf_transformation,[],[f22])).
% 2.70/1.01  
% 2.70/1.01  fof(f57,plain,(
% 2.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f43])).
% 2.70/1.01  
% 2.70/1.01  fof(f13,axiom,(
% 2.70/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 2.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/1.01  
% 2.70/1.01  fof(f38,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.01    inference(ennf_transformation,[],[f13])).
% 2.70/1.01  
% 2.70/1.01  fof(f39,plain,(
% 2.70/1.01    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.01    inference(flattening,[],[f38])).
% 2.70/1.01  
% 2.70/1.01  fof(f76,plain,(
% 2.70/1.01    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f39])).
% 2.70/1.01  
% 2.70/1.01  fof(f70,plain,(
% 2.70/1.01    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f31])).
% 2.70/1.01  
% 2.70/1.01  fof(f69,plain,(
% 2.70/1.01    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f31])).
% 2.70/1.01  
% 2.70/1.01  fof(f63,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f47])).
% 2.70/1.01  
% 2.70/1.01  fof(f62,plain,(
% 2.70/1.01    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK0(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.01    inference(cnf_transformation,[],[f47])).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4311,plain,
% 2.70/1.01      ( k5_tmap_1(X0_60,X0_59) = k5_tmap_1(X1_60,X1_59)
% 2.70/1.01      | X0_60 != X1_60
% 2.70/1.01      | X0_59 != X1_59 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4310,plain,
% 2.70/1.01      ( u1_pre_topc(X0_60) = u1_pre_topc(X1_60) | X0_60 != X1_60 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4295,plain,
% 2.70/1.01      ( X0_62 != X1_62 | X2_62 != X1_62 | X2_62 = X0_62 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4291,plain,( X0_62 = X0_62 ),theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_20,plain,
% 2.70/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.01      | ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X1)
% 2.70/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.70/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_23,plain,
% 2.70/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.01      | ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ l1_pre_topc(X1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_194,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X1)
% 2.70/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.70/1.01      inference(global_propositional_subsumption,[status(thm)],[c_20,c_23]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_195,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | ~ l1_pre_topc(X1)
% 2.70/1.01      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.70/1.01      inference(renaming,[status(thm)],[c_194]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_27,negated_conjecture,
% 2.70/1.01      ( m1_pre_topc(sK3,sK1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1501,plain,
% 2.70/1.01      ( ~ v2_pre_topc(X0)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.01      | sK1 != X0
% 2.70/1.01      | sK3 != X1 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_195,c_27]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1502,plain,
% 2.70/1.01      ( ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | v2_struct_0(sK3)
% 2.70/1.01      | ~ l1_pre_topc(sK1)
% 2.70/1.01      | k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1501]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_33,negated_conjecture,
% 2.70/1.01      ( ~ v2_struct_0(sK1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_32,negated_conjecture,
% 2.70/1.01      ( v2_pre_topc(sK1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_31,negated_conjecture,
% 2.70/1.01      ( l1_pre_topc(sK1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_28,negated_conjecture,
% 2.70/1.01      ( ~ v2_struct_0(sK3) ),
% 2.70/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1504,plain,
% 2.70/1.01      ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.01      inference(global_propositional_subsumption,
% 2.70/1.01                [status(thm)],
% 2.70/1.01                [c_1502,c_33,c_32,c_31,c_28]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4279,plain,
% 2.70/1.01      ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.01      inference(subtyping,[status(esa)],[c_1504]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_29,negated_conjecture,
% 2.70/1.01      ( m1_pre_topc(sK2,sK1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1645,plain,
% 2.70/1.01      ( ~ v2_pre_topc(X0)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.01      | sK2 != X1
% 2.70/1.01      | sK1 != X0 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_195,c_29]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1646,plain,
% 2.70/1.01      ( ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK2)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | ~ l1_pre_topc(sK1)
% 2.70/1.01      | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1645]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_30,negated_conjecture,
% 2.70/1.01      ( ~ v2_struct_0(sK2) ),
% 2.70/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1648,plain,
% 2.70/1.01      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.01      inference(global_propositional_subsumption,
% 2.70/1.01                [status(thm)],
% 2.70/1.01                [c_1646,c_33,c_32,c_31,c_30]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4274,plain,
% 2.70/1.01      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.01      inference(subtyping,[status(esa)],[c_1648]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_352,plain,
% 2.70/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.70/1.01      | r1_tmap_1(X4,X5,X6,X7)
% 2.70/1.01      | X6 != X2
% 2.70/1.01      | X4 != X0
% 2.70/1.01      | X5 != X1
% 2.70/1.01      | X7 != X3 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_349,plain,
% 2.70/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_347,plain,
% 2.70/1.01      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_342,plain,
% 2.70/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_341,plain,
% 2.70/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/1.01      | v1_funct_2(X3,X4,X5)
% 2.70/1.01      | X5 != X2
% 2.70/1.01      | X3 != X0
% 2.70/1.01      | X4 != X1 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_337,plain,
% 2.70/1.01      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.70/1.01      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 2.70/1.01      | X8 != X2
% 2.70/1.01      | X6 != X0
% 2.70/1.01      | X7 != X1
% 2.70/1.01      | X9 != X3
% 2.70/1.01      | X10 != X4
% 2.70/1.01      | X11 != X5 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_336,plain,
% 2.70/1.01      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_335,plain,
% 2.70/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_333,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_332,plain,
% 2.70/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 2.70/1.01      theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_4287,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_8,plain,
% 2.70/1.01      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.01      | ~ m1_pre_topc(X1,X0)
% 2.70/1.01      | ~ v1_pre_topc(X2)
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(X2)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | ~ l1_pre_topc(X2)
% 2.70/1.01      | k8_tmap_1(X0,X1) = X2 ),
% 2.70/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1394,plain,
% 2.70/1.01      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.01      | ~ v1_pre_topc(X2)
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(X2)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | ~ l1_pre_topc(X2)
% 2.70/1.01      | k8_tmap_1(X0,X1) = X2
% 2.70/1.01      | sK1 != X0
% 2.70/1.01      | sK3 != X1 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1395,plain,
% 2.70/1.01      ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | ~ v1_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | ~ l1_pre_topc(sK1)
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1394]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1399,plain,
% 2.70/1.01      ( ~ l1_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ v1_pre_topc(X0)
% 2.70/1.01      | m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.01      inference(global_propositional_subsumption,
% 2.70/1.01                [status(thm)],
% 2.70/1.01                [c_1395,c_33,c_32,c_31]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1400,plain,
% 2.70/1.01      ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | ~ v1_pre_topc(X0)
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.01      inference(renaming,[status(thm)],[c_1399]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_14,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | ~ l1_pre_topc(X1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1683,plain,
% 2.70/1.01      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | sK2 != X1
% 2.70/1.01      | sK1 != X0 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1684,plain,
% 2.70/1.01      ( v1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.01      | ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | ~ l1_pre_topc(sK1) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1683]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1686,plain,
% 2.70/1.01      ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.01      inference(global_propositional_subsumption,
% 2.70/1.01                [status(thm)],
% 2.70/1.01                [c_1684,c_33,c_32,c_31]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_2232,plain,
% 2.70/1.01      ( m1_subset_1(sK0(sK1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | ~ v2_pre_topc(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | k8_tmap_1(sK1,sK2) != X0
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_1400,c_1686]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_2233,plain,
% 2.70/1.01      ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.01      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_2232]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_13,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | ~ l1_pre_topc(X1) ),
% 2.70/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1694,plain,
% 2.70/1.01      ( ~ v2_pre_topc(X0)
% 2.70/1.01      | v2_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | sK2 != X1
% 2.70/1.01      | sK1 != X0 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1695,plain,
% 2.70/1.01      ( v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.01      | ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | ~ l1_pre_topc(sK1) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1694]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_12,plain,
% 2.70/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.01      | ~ v2_pre_topc(X1)
% 2.70/1.01      | v2_struct_0(X1)
% 2.70/1.01      | ~ l1_pre_topc(X1)
% 2.70/1.01      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.70/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1705,plain,
% 2.70/1.01      ( ~ v2_pre_topc(X0)
% 2.70/1.01      | v2_struct_0(X0)
% 2.70/1.01      | ~ l1_pre_topc(X0)
% 2.70/1.01      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.01      | sK2 != X1
% 2.70/1.01      | sK1 != X0 ),
% 2.70/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_1706,plain,
% 2.70/1.01      ( ~ v2_pre_topc(sK1)
% 2.70/1.01      | v2_struct_0(sK1)
% 2.70/1.01      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.01      | ~ l1_pre_topc(sK1) ),
% 2.70/1.01      inference(unflattening,[status(thm)],[c_1705]) ).
% 2.70/1.01  
% 2.70/1.01  cnf(c_2235,plain,
% 2.70/1.01      ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.01      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.01      inference(global_propositional_subsumption,
% 2.70/1.01                [status(thm)],
% 2.70/1.01                [c_2233,c_33,c_32,c_31,c_1695,c_1706]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4261,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2235]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4738,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
% 2.70/1.02      | m1_subset_1(sK0(sK1,sK3,k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4261]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.70/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1997,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.70/1.02      | sK1 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_33]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1998,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1997]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2002,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1998,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4268,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k7_tmap_1(sK1,X0_59) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2002]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4735,plain,
% 2.70/1.02      ( k7_tmap_1(sK1,X0_59) = k6_partfun1(u1_struct_0(sK1))
% 2.70/1.02      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4268]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5954,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k7_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4738,c_4735]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1653,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | sK2 != X0
% 2.70/1.02      | sK1 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1654,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1653]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1656,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1654,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4273,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1656]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4731,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4273]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5324,plain,
% 2.70/1.02      ( k7_tmap_1(sK1,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4731,c_4735]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_11,plain,
% 2.70/1.02      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.70/1.02      | ~ r1_tsep_1(X0,X1)
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X1) ),
% 2.70/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_19,plain,
% 2.70/1.02      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 2.70/1.02      | ~ r1_xboole_0(u1_struct_0(X0),X2)
% 2.70/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.70/1.02      | ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X1) ),
% 2.70/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_24,negated_conjecture,
% 2.70/1.02      ( ~ r1_tmap_1(sK3,k8_tmap_1(sK1,sK2),k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK4) ),
% 2.70/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_389,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(X0),X1)
% 2.70/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.70/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.70/1.02      | ~ m1_pre_topc(X0,X2)
% 2.70/1.02      | ~ v2_pre_topc(X2)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X2)
% 2.70/1.02      | ~ l1_pre_topc(X2)
% 2.70/1.02      | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(X2,X1) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | sK4 != X3
% 2.70/1.02      | sK3 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_390,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.70/1.02      | ~ m1_pre_topc(sK3,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(sK3)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_389]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_25,negated_conjecture,
% 2.70/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.70/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_394,plain,
% 2.70/1.02      ( v2_struct_0(X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ m1_pre_topc(sK3,X1)
% 2.70/1.02      | ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_390,c_28,c_25]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_395,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ m1_pre_topc(sK3,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_394]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1781,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(X1,X0) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | sK1 != X1
% 2.70/1.02      | sK3 != sK3 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_395]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1782,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1781]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1786,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1782,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1787,plain,
% 2.70/1.02      ( ~ r1_xboole_0(u1_struct_0(sK3),X0)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,X0) != k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1786]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2085,plain,
% 2.70/1.02      ( ~ r1_tsep_1(X0,X1)
% 2.70/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X1)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,X2),k7_tmap_1(sK1,X2),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,X2) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X1) != X2
% 2.70/1.02      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_1787]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2086,plain,
% 2.70/1.02      ( ~ r1_tsep_1(X0,X1)
% 2.70/1.02      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X1)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X1)),k7_tmap_1(sK1,u1_struct_0(X1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(X1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2085]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4267,plain,
% 2.70/1.02      ( ~ r1_tsep_1(X0_60,X1_60)
% 2.70/1.02      | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ l1_struct_0(X0_60)
% 2.70/1.02      | ~ l1_struct_0(X1_60)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X1_60)),k7_tmap_1(sK1,u1_struct_0(X1_60)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(X1_60)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2086]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4736,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(X0_60)),k7_tmap_1(sK1,u1_struct_0(X0_60)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(X0_60)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X1_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X1_60,X0_60) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X1_60) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4267]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5836,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK2)),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK2)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK2) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(sK2) != iProver_top ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_5324,c_4736]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_9,plain,
% 2.70/1.02      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.70/1.02      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_211,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_9,c_23,c_14,c_13,c_12]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_212,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_211]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1637,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_212,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1638,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1637]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1640,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1638,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4275,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1640]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5837,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK2) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(sK2) != iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_5836,c_4275]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5838,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK2) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(sK2) != iProver_top ),
% 2.70/1.02      inference(equality_resolution_simp,[status(thm)],[c_5837]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_36,plain,
% 2.70/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1655,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.70/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_0,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1770,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X1 | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1771,plain,
% 2.70/1.02      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1770]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1773,plain,
% 2.70/1.02      ( l1_pre_topc(sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1771,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2288,plain,
% 2.70/1.02      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1773]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2289,plain,
% 2.70/1.02      ( l1_struct_0(sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2288]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2290,plain,
% 2.70/1.02      ( l1_struct_0(sK2) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_2289]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5875,plain,
% 2.70/1.02      ( l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK2) != iProver_top ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_5838,c_36,c_1655,c_2290]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5876,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK2) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_5875]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1466,plain,
% 2.70/1.02      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.02      | ~ v1_pre_topc(X2)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X2)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X2)
% 2.70/1.02      | k8_tmap_1(X0,X1) = X2
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1467,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1466]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1471,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1467,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1472,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1471]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1539,plain,
% 2.70/1.02      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1540,plain,
% 2.70/1.02      ( v1_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1539]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1542,plain,
% 2.70/1.02      ( v1_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1540,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2188,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1472,c_1542]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2189,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2188]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1550,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1551,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1550]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1561,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1562,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | l1_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1561]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2191,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2189,c_33,c_32,c_31,c_1551,c_1562]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4264,plain,
% 2.70/1.02      ( m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2191]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4737,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3)
% 2.70/1.02      | m1_subset_1(sK0(sK1,sK2,k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4264]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5825,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k7_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4737,c_4735]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1509,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | sK1 != X1
% 2.70/1.02      | sK3 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1510,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1509]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1512,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1510,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4278,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1512]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4729,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4278]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5323,plain,
% 2.70/1.02      ( k7_tmap_1(sK1,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK1)) ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4729,c_4735]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1493,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_212,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1494,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1493]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1496,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1494,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4280,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1496]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5419,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK3)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK3) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(sK3) != iProver_top ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4280,c_4736]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5477,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK3) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(sK3) != iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_5419,c_4280]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1511,plain,
% 2.70/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.70/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1626,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1627,plain,
% 2.70/1.02      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1626]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1629,plain,
% 2.70/1.02      ( l1_pre_topc(sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1627,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2274,plain,
% 2.70/1.02      ( l1_struct_0(X0) | sK3 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1629]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2275,plain,
% 2.70/1.02      ( l1_struct_0(sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2274]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2276,plain,
% 2.70/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_2275]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5616,plain,
% 2.70/1.02      ( l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK3) != iProver_top ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_5477,c_36,c_1511,c_2276]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5617,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k7_tmap_1(sK1,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK3) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_5616]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5749,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k8_tmap_1(sK1,sK3),k6_partfun1(u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,sK3) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(demodulation,[status(thm)],[c_5323,c_5617]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_21,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.70/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1520,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1521,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | v2_struct_0(sK3)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1520]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1523,plain,
% 2.70/1.02      ( u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1521,c_33,c_32,c_31,c_28]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4277,plain,
% 2.70/1.02      ( u1_struct_0(k8_tmap_1(sK1,sK3)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1523]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5423,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(k8_tmap_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(k8_tmap_1(sK1,sK3)) != iProver_top ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4277,c_4736]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5447,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(k8_tmap_1(sK1,sK3)) != iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_5423,c_4277]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1564,plain,
% 2.70/1.02      ( l1_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1562,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2267,plain,
% 2.70/1.02      ( l1_struct_0(X0) | k8_tmap_1(sK1,sK3) != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1564]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2268,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2267]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2269,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK3)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5689,plain,
% 2.70/1.02      ( l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5447,c_2269]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5690,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK3)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_5689]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1664,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1665,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK2)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1664]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1667,plain,
% 2.70/1.02      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1665,c_33,c_32,c_31,c_30]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4272,plain,
% 2.70/1.02      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1667]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5424,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(k8_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4272,c_4736]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5432,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_5424,c_4272]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1708,plain,
% 2.70/1.02      ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1706,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2281,plain,
% 2.70/1.02      ( l1_struct_0(X0) | k8_tmap_1(sK1,sK2) != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1708]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2282,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2281]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2283,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5676,plain,
% 2.70/1.02      ( l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5432,c_2283]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5677,plain,
% 2.70/1.02      ( k2_tmap_1(sK1,k6_tmap_1(sK1,u1_struct_0(sK1)),k7_tmap_1(sK1,u1_struct_0(sK1)),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
% 2.70/1.02      | k6_tmap_1(sK1,u1_struct_0(sK1)) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | u1_struct_0(X0_60) != u1_struct_0(sK3)
% 2.70/1.02      | r1_tsep_1(X0_60,k8_tmap_1(sK1,sK2)) != iProver_top
% 2.70/1.02      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_5676]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_26,negated_conjecture,
% 2.70/1.02      ( r1_tsep_1(sK2,sK3) ),
% 2.70/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4284,negated_conjecture,
% 2.70/1.02      ( r1_tsep_1(sK2,sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_26]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4725,plain,
% 2.70/1.02      ( r1_tsep_1(sK2,sK3) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4284]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_18,plain,
% 2.70/1.02      ( ~ r1_tsep_1(X0,X1)
% 2.70/1.02      | r1_tsep_1(X1,X0)
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X1) ),
% 2.70/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4286,plain,
% 2.70/1.02      ( ~ r1_tsep_1(X0_60,X1_60)
% 2.70/1.02      | r1_tsep_1(X1_60,X0_60)
% 2.70/1.02      | ~ l1_struct_0(X0_60)
% 2.70/1.02      | ~ l1_struct_0(X1_60) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4723,plain,
% 2.70/1.02      ( r1_tsep_1(X0_60,X1_60) != iProver_top
% 2.70/1.02      | r1_tsep_1(X1_60,X0_60) = iProver_top
% 2.70/1.02      | l1_struct_0(X0_60) != iProver_top
% 2.70/1.02      | l1_struct_0(X1_60) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4286]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4993,plain,
% 2.70/1.02      ( r1_tsep_1(sK3,sK2) = iProver_top
% 2.70/1.02      | l1_struct_0(sK2) != iProver_top
% 2.70/1.02      | l1_struct_0(sK3) != iProver_top ),
% 2.70/1.02      inference(superposition,[status(thm)],[c_4725,c_4723]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_41,plain,
% 2.70/1.02      ( r1_tsep_1(sK2,sK3) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4947,plain,
% 2.70/1.02      ( ~ r1_tsep_1(sK2,sK3)
% 2.70/1.02      | r1_tsep_1(sK3,sK2)
% 2.70/1.02      | ~ l1_struct_0(sK2)
% 2.70/1.02      | ~ l1_struct_0(sK3) ),
% 2.70/1.02      inference(instantiation,[status(thm)],[c_4286]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4948,plain,
% 2.70/1.02      ( r1_tsep_1(sK2,sK3) != iProver_top
% 2.70/1.02      | r1_tsep_1(sK3,sK2) = iProver_top
% 2.70/1.02      | l1_struct_0(sK2) != iProver_top
% 2.70/1.02      | l1_struct_0(sK3) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4947]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_5027,plain,
% 2.70/1.02      ( r1_tsep_1(sK3,sK2) = iProver_top ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_4993,c_41,c_2276,c_2290,c_4948]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_15,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1455,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1456,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1455]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1458,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1456,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4281,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1458]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4728,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4281]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4785,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_4728,c_4272]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1383,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1384,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3)))))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1383]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1386,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1384,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4282,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1386]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4727,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))))) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4282]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4782,plain,
% 2.70/1.02      ( m1_subset_1(k9_tmap_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.70/1.02      inference(light_normalisation,[status(thm)],[c_4727,c_4277]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2,plain,
% 2.70/1.02      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4,plain,
% 2.70/1.02      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.70/1.02      | ~ v1_funct_2(X5,X2,X3)
% 2.70/1.02      | ~ v1_funct_2(X4,X0,X1)
% 2.70/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.70/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/1.02      | ~ v1_funct_1(X5)
% 2.70/1.02      | ~ v1_funct_1(X4)
% 2.70/1.02      | v1_xboole_0(X1)
% 2.70/1.02      | v1_xboole_0(X3)
% 2.70/1.02      | X4 = X5 ),
% 2.70/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_22,plain,
% 2.70/1.02      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_476,plain,
% 2.70/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/1.02      | ~ v1_funct_2(X3,X4,X5)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.70/1.02      | ~ m1_pre_topc(X6,X7)
% 2.70/1.02      | ~ v2_pre_topc(X7)
% 2.70/1.02      | ~ v1_funct_1(X0)
% 2.70/1.02      | ~ v1_funct_1(X3)
% 2.70/1.02      | v2_struct_0(X7)
% 2.70/1.02      | v2_struct_0(X6)
% 2.70/1.02      | v1_xboole_0(X2)
% 2.70/1.02      | v1_xboole_0(X5)
% 2.70/1.02      | ~ l1_pre_topc(X7)
% 2.70/1.02      | X3 = X0
% 2.70/1.02      | k9_tmap_1(X7,X6) != X0
% 2.70/1.02      | k3_struct_0(X7) != X3
% 2.70/1.02      | u1_struct_0(X7) != X5
% 2.70/1.02      | u1_struct_0(X7) != X4
% 2.70/1.02      | u1_struct_0(X7) != X1
% 2.70/1.02      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_477,plain,
% 2.70/1.02      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(X0))
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_476]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_16,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0) ),
% 2.70/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_481,plain,
% 2.70/1.02      ( v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_477,c_16,c_15,c_2,c_0]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_482,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_481]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_17,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1) ),
% 2.70/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_509,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ m1_pre_topc(X1,X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 2.70/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_482,c_17]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1421,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_509,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1422,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(sK2)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1421]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1424,plain,
% 2.70/1.02      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1422,c_33,c_32,c_31,c_30]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1425,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1424]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1924,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(X0) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_1425]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_110,plain,
% 2.70/1.02      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.70/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1926,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(instantiation,[status(thm)],[c_1924]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1928,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1924,c_33,c_32,c_31,c_30,c_110,c_1665,c_1926]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1929,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1928]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1372,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1373,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3)))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1372]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1375,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK3))) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1373,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2026,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1929,c_1375]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2028,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2026,c_33,c_32,c_31,c_28,c_1521]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2029,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_2028]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1528,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1529,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v1_funct_1(k9_tmap_1(sK1,sK3))
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1528]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1531,plain,
% 2.70/1.02      ( v1_funct_1(k9_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1529,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2121,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_2029,c_1531]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_3264,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1) ),
% 2.70/1.02      inference(equality_resolution_simp,[status(thm)],[c_2121]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4254,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_3264]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4745,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK2) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) != k3_struct_0(sK1)
% 2.70/1.02      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4254]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1349,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(X0))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 2.70/1.02      | sK1 != X0
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_509,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1350,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | v2_struct_0(sK3)
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1349]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1352,plain,
% 2.70/1.02      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1350,c_33,c_32,c_31,c_28]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1353,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK1,sK3)))
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1352]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1903,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_struct_0(X0)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(X0) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_1353]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1905,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK3)) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(instantiation,[status(thm)],[c_1903]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1907,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1903,c_33,c_32,c_31,c_28,c_110,c_1521,c_1905]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1908,plain,
% 2.70/1.02      ( ~ v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1907]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1444,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1445,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1444]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1447,plain,
% 2.70/1.02      ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1445,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2050,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(k8_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1908,c_1447]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2052,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2050,c_33,c_32,c_31,c_30,c_1665]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2053,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | ~ v1_funct_1(k3_struct_0(sK1))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_2052]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1672,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.70/1.02      | v2_struct_0(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK2 != X1
% 2.70/1.02      | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1673,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK1)
% 2.70/1.02      | v1_funct_1(k9_tmap_1(sK1,sK2))
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1672]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1675,plain,
% 2.70/1.02      ( v1_funct_1(k9_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1673,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2136,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_2053,c_1675]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_3262,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(equality_resolution_simp,[status(thm)],[c_2136]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4255,plain,
% 2.70/1.02      ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.70/1.02      | k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_3262]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4744,plain,
% 2.70/1.02      ( k9_tmap_1(sK1,sK2) != k3_struct_0(sK1)
% 2.70/1.02      | k9_tmap_1(sK1,sK3) = k3_struct_0(sK1)
% 2.70/1.02      | m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4255]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1976,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.70/1.02      | sK2 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_30]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1977,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.70/1.02      | ~ v2_pre_topc(sK2)
% 2.70/1.02      | ~ l1_pre_topc(sK2)
% 2.70/1.02      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1976]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1981,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK2)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.70/1.02      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1977,c_31,c_1771]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1982,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.70/1.02      | ~ v2_pre_topc(sK2)
% 2.70/1.02      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1981]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4269,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.70/1.02      | ~ v2_pre_topc(sK2)
% 2.70/1.02      | k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1982]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4734,plain,
% 2.70/1.02      ( k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2))
% 2.70/1.02      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.70/1.02      | v2_pre_topc(sK2) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4269]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1955,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.70/1.02      | sK3 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1956,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.02      | ~ v2_pre_topc(sK3)
% 2.70/1.02      | ~ l1_pre_topc(sK3)
% 2.70/1.02      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1955]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1960,plain,
% 2.70/1.02      ( ~ v2_pre_topc(sK3)
% 2.70/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.02      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1956,c_31,c_1627]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1961,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.02      | ~ v2_pre_topc(sK3)
% 2.70/1.02      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1960]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4270,plain,
% 2.70/1.02      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.02      | ~ v2_pre_topc(sK3)
% 2.70/1.02      | k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1961]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4733,plain,
% 2.70/1.02      ( k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3))
% 2.70/1.02      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.70/1.02      | v2_pre_topc(sK3) != iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4270]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_6,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v1_pre_topc(X2)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X2)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X2)
% 2.70/1.02      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 2.70/1.02      | k8_tmap_1(X1,X0) = X2 ),
% 2.70/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1743,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(X1,X2) = X0
% 2.70/1.02      | sK2 != X2
% 2.70/1.02      | sK1 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1744,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1743]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1748,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1744,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1749,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1748]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2162,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1749,c_1542]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2163,plain,
% 2.70/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2162]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2165,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2163,c_33,c_32,c_31,c_1551,c_1562]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4266,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,sK0(sK1,sK2,k8_tmap_1(sK1,sK3))) != k8_tmap_1(sK1,sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2165]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_7,plain,
% 2.70/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.70/1.02      | ~ v1_pre_topc(X2)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X2)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X2)
% 2.70/1.02      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 2.70/1.02      | k8_tmap_1(X1,X0) = X2 ),
% 2.70/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1716,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(X1,X2,X0) = u1_struct_0(X2)
% 2.70/1.02      | k8_tmap_1(X1,X2) = X0
% 2.70/1.02      | sK2 != X2
% 2.70/1.02      | sK1 != X1 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1717,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1716]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1721,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1717,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1722,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0 ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1721]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2173,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK2,X0) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1722,c_1542]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2174,plain,
% 2.70/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(sK1,sK3))
% 2.70/1.02      | sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2173]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2176,plain,
% 2.70/1.02      ( sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2174,c_33,c_32,c_31,c_1551,c_1562]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4265,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK2) = k8_tmap_1(sK1,sK3)
% 2.70/1.02      | sK0(sK1,sK2,k8_tmap_1(sK1,sK3)) = u1_struct_0(sK2) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2176]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1599,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
% 2.70/1.02      | k8_tmap_1(X1,X2) = X0
% 2.70/1.02      | sK1 != X1
% 2.70/1.02      | sK3 != X2 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1600,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1599]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1604,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1600,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1605,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1604]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2208,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK3,X0)) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK2) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1605,c_1686]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2209,plain,
% 2.70/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.02      | k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2208]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2211,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2209,c_33,c_32,c_31,c_1695,c_1706]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4263,plain,
% 2.70/1.02      ( k6_tmap_1(sK1,sK0(sK1,sK3,k8_tmap_1(sK1,sK2))) != k8_tmap_1(sK1,sK2)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2211]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1572,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X1)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | v2_struct_0(X1)
% 2.70/1.02      | ~ l1_pre_topc(X1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(X1,X2,X0) = u1_struct_0(X2)
% 2.70/1.02      | k8_tmap_1(X1,X2) = X0
% 2.70/1.02      | sK1 != X1
% 2.70/1.02      | sK3 != X2 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1573,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(sK1)
% 2.70/1.02      | v2_struct_0(sK1)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(sK1)
% 2.70/1.02      | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_1572]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1577,plain,
% 2.70/1.02      ( ~ l1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ v1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1573,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1578,plain,
% 2.70/1.02      ( ~ v1_pre_topc(X0)
% 2.70/1.02      | ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(renaming,[status(thm)],[c_1577]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2219,plain,
% 2.70/1.02      ( ~ v2_pre_topc(X0)
% 2.70/1.02      | ~ l1_pre_topc(X0)
% 2.70/1.02      | sK0(sK1,sK3,X0) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK2) != X0
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_1578,c_1686]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2220,plain,
% 2.70/1.02      ( ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.02      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.70/1.02      | sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2219]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2222,plain,
% 2.70/1.02      ( sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3)
% 2.70/1.02      | k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_2220,c_33,c_32,c_31,c_1695,c_1706]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4262,plain,
% 2.70/1.02      ( k8_tmap_1(sK1,sK3) = k8_tmap_1(sK1,sK2)
% 2.70/1.02      | sK0(sK1,sK3,k8_tmap_1(sK1,sK2)) = u1_struct_0(sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2222]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4256,plain,
% 2.70/1.02      ( l1_struct_0(sK2) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2289]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4743,plain,
% 2.70/1.02      ( l1_struct_0(sK2) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4256]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4257,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2282]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4742,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4257]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4258,plain,
% 2.70/1.02      ( l1_struct_0(sK3) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2275]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4741,plain,
% 2.70/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4258]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4259,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2268]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4740,plain,
% 2.70/1.02      ( l1_struct_0(k8_tmap_1(sK1,sK3)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4259]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2260,plain,
% 2.70/1.02      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.70/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_2261,plain,
% 2.70/1.02      ( l1_struct_0(sK1) ),
% 2.70/1.02      inference(unflattening,[status(thm)],[c_2260]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4260,plain,
% 2.70/1.02      ( l1_struct_0(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_2261]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4739,plain,
% 2.70/1.02      ( l1_struct_0(sK1) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4260]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1697,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1695,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4271,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1697]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4732,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4271]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_1553,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(global_propositional_subsumption,
% 2.70/1.02                [status(thm)],
% 2.70/1.02                [c_1551,c_33,c_32,c_31]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4276,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK3)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_1553]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4730,plain,
% 2.70/1.02      ( v2_pre_topc(k8_tmap_1(sK1,sK3)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4276]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4285,negated_conjecture,
% 2.70/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4724,plain,
% 2.70/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4285]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4283,negated_conjecture,
% 2.70/1.02      ( v2_pre_topc(sK1) ),
% 2.70/1.02      inference(subtyping,[status(esa)],[c_32]) ).
% 2.70/1.02  
% 2.70/1.02  cnf(c_4726,plain,
% 2.70/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.70/1.02      inference(predicate_to_equality,[status(thm)],[c_4283]) ).
% 2.70/1.02  
% 2.70/1.02  
% 2.70/1.02  % SZS output end Saturation for theBenchmark.p
% 2.70/1.02  
% 2.70/1.02  ------                               Statistics
% 2.70/1.02  
% 2.70/1.02  ------ General
% 2.70/1.02  
% 2.70/1.02  abstr_ref_over_cycles:                  0
% 2.70/1.02  abstr_ref_under_cycles:                 0
% 2.70/1.02  gc_basic_clause_elim:                   0
% 2.70/1.02  forced_gc_time:                         0
% 2.70/1.02  parsing_time:                           0.017
% 2.70/1.02  unif_index_cands_time:                  0.
% 2.70/1.02  unif_index_add_time:                    0.
% 2.70/1.02  orderings_time:                         0.
% 2.70/1.02  out_proof_time:                         0.
% 2.70/1.02  total_time:                             0.221
% 2.70/1.02  num_of_symbols:                         69
% 2.70/1.02  num_of_terms:                           4001
% 2.70/1.02  
% 2.70/1.02  ------ Preprocessing
% 2.70/1.02  
% 2.70/1.02  num_of_splits:                          0
% 2.70/1.02  num_of_split_atoms:                     0
% 2.70/1.02  num_of_reused_defs:                     0
% 2.70/1.02  num_eq_ax_congr_red:                    9
% 2.70/1.02  num_of_sem_filtered_clauses:            7
% 2.70/1.02  num_of_subtypes:                        4
% 2.70/1.02  monotx_restored_types:                  0
% 2.70/1.02  sat_num_of_epr_types:                   0
% 2.70/1.02  sat_num_of_non_cyclic_types:            0
% 2.70/1.02  sat_guarded_non_collapsed_types:        0
% 2.70/1.02  num_pure_diseq_elim:                    0
% 2.70/1.02  simp_replaced_by:                       0
% 2.70/1.02  res_preprocessed:                       178
% 2.70/1.02  prep_upred:                             0
% 2.70/1.02  prep_unflattend:                        151
% 2.70/1.02  smt_new_axioms:                         0
% 2.70/1.02  pred_elim_cands:                        4
% 2.70/1.02  pred_elim:                              10
% 2.70/1.02  pred_elim_cl:                           1
% 2.70/1.02  pred_elim_cycles:                       20
% 2.70/1.02  merged_defs:                            0
% 2.70/1.02  merged_defs_ncl:                        0
% 2.70/1.02  bin_hyper_res:                          0
% 2.70/1.02  prep_cycles:                            4
% 2.70/1.02  pred_elim_time:                         0.081
% 2.70/1.02  splitting_time:                         0.
% 2.70/1.02  sem_filter_time:                        0.
% 2.70/1.02  monotx_time:                            0.
% 2.70/1.02  subtype_inf_time:                       0.
% 2.70/1.02  
% 2.70/1.02  ------ Problem properties
% 2.70/1.02  
% 2.70/1.02  clauses:                                33
% 2.70/1.02  conjectures:                            3
% 2.70/1.02  epr:                                    6
% 2.70/1.02  horn:                                   29
% 2.70/1.02  ground:                                 28
% 2.70/1.02  unary:                                  20
% 2.70/1.02  binary:                                 7
% 2.70/1.02  lits:                                   57
% 2.70/1.02  lits_eq:                                26
% 2.70/1.02  fd_pure:                                0
% 2.70/1.02  fd_pseudo:                              0
% 2.70/1.02  fd_cond:                                0
% 2.70/1.02  fd_pseudo_cond:                         0
% 2.70/1.02  ac_symbols:                             0
% 2.70/1.02  
% 2.70/1.02  ------ Propositional Solver
% 2.70/1.02  
% 2.70/1.02  prop_solver_calls:                      28
% 2.70/1.02  prop_fast_solver_calls:                 2043
% 2.70/1.02  smt_solver_calls:                       0
% 2.70/1.02  smt_fast_solver_calls:                  0
% 2.70/1.02  prop_num_of_clauses:                    1143
% 2.70/1.02  prop_preprocess_simplified:             4558
% 2.70/1.02  prop_fo_subsumed:                       141
% 2.70/1.02  prop_solver_time:                       0.
% 2.70/1.02  smt_solver_time:                        0.
% 2.70/1.02  smt_fast_solver_time:                   0.
% 2.70/1.02  prop_fast_solver_time:                  0.
% 2.70/1.02  prop_unsat_core_time:                   0.
% 2.70/1.02  
% 2.70/1.02  ------ QBF
% 2.70/1.02  
% 2.70/1.02  qbf_q_res:                              0
% 2.70/1.02  qbf_num_tautologies:                    0
% 2.70/1.02  qbf_prep_cycles:                        0
% 2.70/1.02  
% 2.70/1.02  ------ BMC1
% 2.70/1.02  
% 2.70/1.02  bmc1_current_bound:                     -1
% 2.70/1.02  bmc1_last_solved_bound:                 -1
% 2.70/1.02  bmc1_unsat_core_size:                   -1
% 2.70/1.02  bmc1_unsat_core_parents_size:           -1
% 2.70/1.02  bmc1_merge_next_fun:                    0
% 2.70/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.02  
% 2.70/1.02  ------ Instantiation
% 2.70/1.02  
% 2.70/1.02  inst_num_of_clauses:                    272
% 2.70/1.02  inst_num_in_passive:                    12
% 2.70/1.02  inst_num_in_active:                     206
% 2.70/1.02  inst_num_in_unprocessed:                54
% 2.70/1.02  inst_num_of_loops:                      220
% 2.70/1.02  inst_num_of_learning_restarts:          0
% 2.70/1.02  inst_num_moves_active_passive:          10
% 2.70/1.02  inst_lit_activity:                      0
% 2.70/1.02  inst_lit_activity_moves:                0
% 2.70/1.02  inst_num_tautologies:                   0
% 2.70/1.02  inst_num_prop_implied:                  0
% 2.70/1.02  inst_num_existing_simplified:           0
% 2.70/1.02  inst_num_eq_res_simplified:             0
% 2.70/1.02  inst_num_child_elim:                    0
% 2.70/1.02  inst_num_of_dismatching_blockings:      44
% 2.70/1.02  inst_num_of_non_proper_insts:           254
% 2.70/1.02  inst_num_of_duplicates:                 0
% 2.70/1.02  inst_inst_num_from_inst_to_res:         0
% 2.70/1.02  inst_dismatching_checking_time:         0.
% 2.70/1.02  
% 2.70/1.02  ------ Resolution
% 2.70/1.02  
% 2.70/1.02  res_num_of_clauses:                     0
% 2.70/1.02  res_num_in_passive:                     0
% 2.70/1.02  res_num_in_active:                      0
% 2.70/1.02  res_num_of_loops:                       182
% 2.70/1.02  res_forward_subset_subsumed:            79
% 2.70/1.02  res_backward_subset_subsumed:           0
% 2.70/1.02  res_forward_subsumed:                   1
% 2.70/1.02  res_backward_subsumed:                  0
% 2.70/1.02  res_forward_subsumption_resolution:     7
% 2.70/1.02  res_backward_subsumption_resolution:    0
% 2.70/1.02  res_clause_to_clause_subsumption:       237
% 2.70/1.02  res_orphan_elimination:                 0
% 2.70/1.02  res_tautology_del:                      75
% 2.70/1.02  res_num_eq_res_simplified:              2
% 2.70/1.02  res_num_sel_changes:                    0
% 2.70/1.02  res_moves_from_active_to_pass:          0
% 2.70/1.02  
% 2.70/1.02  ------ Superposition
% 2.70/1.02  
% 2.70/1.02  sup_time_total:                         0.
% 2.70/1.02  sup_time_generating:                    0.
% 2.70/1.02  sup_time_sim_full:                      0.
% 2.70/1.02  sup_time_sim_immed:                     0.
% 2.70/1.02  
% 2.70/1.02  sup_num_of_clauses:                     42
% 2.70/1.02  sup_num_in_active:                      42
% 2.70/1.02  sup_num_in_passive:                     0
% 2.70/1.02  sup_num_of_loops:                       43
% 2.70/1.02  sup_fw_superposition:                   14
% 2.70/1.02  sup_bw_superposition:                   6
% 2.70/1.02  sup_immediate_simplified:               13
% 2.70/1.02  sup_given_eliminated:                   0
% 2.70/1.02  comparisons_done:                       0
% 2.70/1.02  comparisons_avoided:                    6
% 2.70/1.02  
% 2.70/1.02  ------ Simplifications
% 2.70/1.02  
% 2.70/1.02  
% 2.70/1.02  sim_fw_subset_subsumed:                 5
% 2.70/1.02  sim_bw_subset_subsumed:                 0
% 2.70/1.02  sim_fw_subsumed:                        0
% 2.70/1.02  sim_bw_subsumed:                        0
% 2.70/1.02  sim_fw_subsumption_res:                 0
% 2.70/1.02  sim_bw_subsumption_res:                 0
% 2.70/1.02  sim_tautology_del:                      2
% 2.70/1.02  sim_eq_tautology_del:                   0
% 2.70/1.02  sim_eq_res_simp:                        2
% 2.70/1.02  sim_fw_demodulated:                     0
% 2.70/1.02  sim_bw_demodulated:                     1
% 2.70/1.02  sim_light_normalised:                   11
% 2.70/1.02  sim_joinable_taut:                      0
% 2.70/1.02  sim_joinable_simp:                      0
% 2.70/1.02  sim_ac_normalised:                      0
% 2.70/1.02  sim_smt_subsumption:                    0
% 2.70/1.02  
%------------------------------------------------------------------------------
