%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:01 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 475 expanded)
%              Number of clauses        :   66 ( 110 expanded)
%              Number of leaves         :   12 ( 149 expanded)
%              Depth                    :   26
%              Number of atoms          :  592 (3506 expanded)
%              Number of equality atoms :  112 ( 476 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f37,plain,
    ( ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
      | ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) )
    & u1_struct_0(sK2) = u1_struct_0(sK3)
    & m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f36,f35,f34])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
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
    inference(equality_resolution,[],[f40])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f64,plain,
    ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    | ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_878,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_879,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_881,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_879,c_24])).

cnf(c_2516,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_881])).

cnf(c_3419,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

cnf(c_20,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2520,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3485,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3419,c_2520])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_1228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_25,c_24])).

cnf(c_2507,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0_47)) = k5_tmap_1(sK1,X0_47) ),
    inference(subtyping,[status(esa)],[c_1232])).

cnf(c_3432,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0_47)) = k5_tmap_1(sK1,X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2507])).

cnf(c_4928,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) = k5_tmap_1(sK1,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_3485,c_3432])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_177,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_18,c_11,c_10,c_9])).

cnf(c_178,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_870,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_22])).

cnf(c_871,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_873,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_26,c_25,c_24])).

cnf(c_2517,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_873])).

cnf(c_3482,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2517,c_2520])).

cnf(c_4939,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4928,c_3482])).

cnf(c_931,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_932,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_934,plain,
    ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_26,c_25,c_24])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_722,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_723,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_941,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_934,c_723])).

cnf(c_900,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_901,plain,
    ( v2_struct_0(sK1)
    | v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_26,c_25,c_24])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,k5_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_161,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_18])).

cnf(c_162,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_19,negated_conjecture,
    ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2))
    | ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_148,negated_conjecture,
    ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_306,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK1,sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_148])).

cnf(c_307,plain,
    ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_309,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_21])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | k8_tmap_1(sK1,sK2) != X1
    | u1_struct_0(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_309])).

cnf(c_329,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(k8_tmap_1(sK1,sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_struct_0(sK3) != X0
    | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X1,X0) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_329])).

cnf(c_350,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_903,c_350])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_934,c_1051])).

cnf(c_1063,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_941,c_1057])).

cnf(c_1418,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1063])).

cnf(c_1419,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1418])).

cnf(c_1421,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1419,c_25,c_24])).

cnf(c_2500,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_1421])).

cnf(c_3438,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2500])).

cnf(c_3588,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3438,c_3485])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4939,c_3588])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:44:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.33/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.00  
% 2.33/1.00  ------  iProver source info
% 2.33/1.00  
% 2.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.00  git: non_committed_changes: false
% 2.33/1.00  git: last_make_outside_of_git: false
% 2.33/1.00  
% 2.33/1.00  ------ 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options
% 2.33/1.00  
% 2.33/1.00  --out_options                           all
% 2.33/1.00  --tptp_safe_out                         true
% 2.33/1.00  --problem_path                          ""
% 2.33/1.00  --include_path                          ""
% 2.33/1.00  --clausifier                            res/vclausify_rel
% 2.33/1.00  --clausifier_options                    --mode clausify
% 2.33/1.00  --stdin                                 false
% 2.33/1.00  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     num_symb
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       true
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  ------ Parsing...
% 2.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... gs_s  sp: 13 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.00  ------ Proving...
% 2.33/1.00  ------ Problem Properties 
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  clauses                                 67
% 2.33/1.00  conjectures                             3
% 2.33/1.00  EPR                                     9
% 2.33/1.00  Horn                                    47
% 2.33/1.00  unary                                   8
% 2.33/1.00  binary                                  11
% 2.33/1.00  lits                                    196
% 2.33/1.00  lits eq                                 90
% 2.33/1.00  fd_pure                                 0
% 2.33/1.00  fd_pseudo                               0
% 2.33/1.00  fd_cond                                 0
% 2.33/1.00  fd_pseudo_cond                          0
% 2.33/1.00  AC symbols                              0
% 2.33/1.00  
% 2.33/1.00  ------ Schedule dynamic 5 is on 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ 
% 2.33/1.00  Current options:
% 2.33/1.00  ------ 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options
% 2.33/1.00  
% 2.33/1.00  --out_options                           all
% 2.33/1.00  --tptp_safe_out                         true
% 2.33/1.00  --problem_path                          ""
% 2.33/1.00  --include_path                          ""
% 2.33/1.00  --clausifier                            res/vclausify_rel
% 2.33/1.00  --clausifier_options                    --mode clausify
% 2.33/1.00  --stdin                                 false
% 2.33/1.00  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     none
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       false
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ Proving...
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS status Theorem for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  fof(f8,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f24,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f8])).
% 2.33/1.00  
% 2.33/1.00  fof(f56,plain,(
% 2.33/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f24])).
% 2.33/1.00  
% 2.33/1.00  fof(f9,conjecture,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f10,negated_conjecture,(
% 2.33/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 2.33/1.00    inference(negated_conjecture,[],[f9])).
% 2.33/1.00  
% 2.33/1.00  fof(f25,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : (? [X2] : (((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2)) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f10])).
% 2.33/1.00  
% 2.33/1.00  fof(f26,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f25])).
% 2.33/1.00  
% 2.33/1.00  fof(f36,plain,(
% 2.33/1.00    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) => ((~m1_pre_topc(sK3,k8_tmap_1(X0,X1)) | ~v1_tsep_1(sK3,k8_tmap_1(X0,X1))) & u1_struct_0(sK3) = u1_struct_0(X1) & m1_pre_topc(sK3,k8_tmap_1(X0,X1)))) )),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f35,plain,(
% 2.33/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,sK2)) | ~v1_tsep_1(X2,k8_tmap_1(X0,sK2))) & u1_struct_0(sK2) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,sK2))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f34,plain,(
% 2.33/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(sK1,X1)) | ~v1_tsep_1(X2,k8_tmap_1(sK1,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(sK1,X1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f37,plain,(
% 2.33/1.00    (((~m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) | ~v1_tsep_1(sK3,k8_tmap_1(sK1,sK2))) & u1_struct_0(sK2) = u1_struct_0(sK3) & m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f36,f35,f34])).
% 2.33/1.00  
% 2.33/1.00  fof(f61,plain,(
% 2.33/1.00    m1_pre_topc(sK2,sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f59,plain,(
% 2.33/1.00    l1_pre_topc(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f63,plain,(
% 2.33/1.00    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f6,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f20,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f6])).
% 2.33/1.00  
% 2.33/1.00  fof(f21,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f20])).
% 2.33/1.00  
% 2.33/1.00  fof(f52,plain,(
% 2.33/1.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f21])).
% 2.33/1.00  
% 2.33/1.00  fof(f57,plain,(
% 2.33/1.00    ~v2_struct_0(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f58,plain,(
% 2.33/1.00    v2_pre_topc(sK1)),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f2,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f12,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f2])).
% 2.33/1.00  
% 2.33/1.00  fof(f13,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f12])).
% 2.33/1.00  
% 2.33/1.00  fof(f28,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f13])).
% 2.33/1.00  
% 2.33/1.00  fof(f29,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(rectify,[],[f28])).
% 2.33/1.00  
% 2.33/1.00  fof(f30,plain,(
% 2.33/1.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f31,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.33/1.00  
% 2.33/1.00  fof(f40,plain,(
% 2.33/1.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f31])).
% 2.33/1.00  
% 2.33/1.00  fof(f65,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(equality_resolution,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f66,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(equality_resolution,[],[f65])).
% 2.33/1.00  
% 2.33/1.00  fof(f4,axiom,(
% 2.33/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f16,plain,(
% 2.33/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f4])).
% 2.33/1.00  
% 2.33/1.00  fof(f17,plain,(
% 2.33/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f16])).
% 2.33/1.00  
% 2.33/1.00  fof(f47,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f48,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f49,plain,(
% 2.33/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f62,plain,(
% 2.33/1.00    m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f5,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r2_hidden(X1,k5_tmap_1(X0,X1))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f18,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f5])).
% 2.33/1.00  
% 2.33/1.00  fof(f19,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/1.00    inference(flattening,[],[f18])).
% 2.33/1.00  
% 2.33/1.00  fof(f50,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f19])).
% 2.33/1.00  
% 2.33/1.00  fof(f1,axiom,(
% 2.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f11,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f1])).
% 2.33/1.00  
% 2.33/1.00  fof(f27,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f11])).
% 2.33/1.00  
% 2.33/1.00  fof(f39,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f27])).
% 2.33/1.00  
% 2.33/1.00  fof(f7,axiom,(
% 2.33/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f22,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f7])).
% 2.33/1.00  
% 2.33/1.00  fof(f23,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f22])).
% 2.33/1.00  
% 2.33/1.00  fof(f32,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f23])).
% 2.33/1.00  
% 2.33/1.00  fof(f33,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.33/1.00    inference(flattening,[],[f32])).
% 2.33/1.00  
% 2.33/1.00  fof(f54,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f33])).
% 2.33/1.00  
% 2.33/1.00  fof(f68,plain,(
% 2.33/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.33/1.00    inference(equality_resolution,[],[f54])).
% 2.33/1.00  
% 2.33/1.00  fof(f64,plain,(
% 2.33/1.00    ~m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) | ~v1_tsep_1(sK3,k8_tmap_1(sK1,sK2))),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  cnf(c_18,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,negated_conjecture,
% 2.33/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_878,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | sK2 != X0
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_879,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ l1_pre_topc(sK1) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_878]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_24,negated_conjecture,
% 2.33/1.00      ( l1_pre_topc(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_881,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_879,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2516,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_881]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3419,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2516]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,negated_conjecture,
% 2.33/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2520,negated_conjecture,
% 2.33/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3485,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_3419,c_2520]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_13,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_26,negated_conjecture,
% 2.33/1.00      ( ~ v2_struct_0(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1227,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.33/1.00      | sK1 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1228,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1)
% 2.33/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_1227]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,negated_conjecture,
% 2.33/1.00      ( v2_pre_topc(sK1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1232,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1228,c_25,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2507,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0_47)) = k5_tmap_1(sK1,X0_47) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_1232]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3432,plain,
% 2.33/1.00      ( u1_pre_topc(k6_tmap_1(sK1,X0_47)) = k5_tmap_1(sK1,X0_47)
% 2.33/1.00      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2507]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4928,plain,
% 2.33/1.00      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK3))) = k5_tmap_1(sK1,u1_struct_0(sK3)) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3485,c_3432]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_5,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.33/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_11,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_10,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_9,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_177,plain,
% 2.33/1.00      ( ~ l1_pre_topc(X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_5,c_18,c_11,c_10,c_9]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_178,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_177]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_870,plain,
% 2.33/1.00      ( v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.33/1.00      | sK2 != X1
% 2.33/1.00      | sK1 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_178,c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_871,plain,
% 2.33/1.00      ( v2_struct_0(sK1)
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1)
% 2.33/1.00      | k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_870]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_873,plain,
% 2.33/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_871,c_26,c_25,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2517,plain,
% 2.33/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_873]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3482,plain,
% 2.33/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK3)) = k8_tmap_1(sK1,sK2) ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_2517,c_2520]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4939,plain,
% 2.33/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_4928,c_3482]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_931,plain,
% 2.33/1.00      ( v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.33/1.00      | sK2 != X1
% 2.33/1.00      | sK1 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_932,plain,
% 2.33/1.00      ( v2_struct_0(sK1)
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(sK1) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_931]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_934,plain,
% 2.33/1.00      ( l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_932,c_26,c_25,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_21,negated_conjecture,
% 2.33/1.00      ( m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_722,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | k8_tmap_1(sK1,sK2) != X1
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_723,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_722]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_941,plain,
% 2.33/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2)))) ),
% 2.33/1.00      inference(backward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_934,c_723]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_900,plain,
% 2.33/1.00      ( v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | v2_pre_topc(k8_tmap_1(X0,X1))
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | sK2 != X1
% 2.33/1.00      | sK1 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_901,plain,
% 2.33/1.00      ( v2_struct_0(sK1)
% 2.33/1.00      | v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_900]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_903,plain,
% 2.33/1.00      ( v2_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_901,c_26,c_25,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_12,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | r2_hidden(X0,k5_tmap_1(X1,X0))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.33/1.00      | v3_pre_topc(X0,X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( v1_tsep_1(X0,X1)
% 2.33/1.00      | ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_161,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | v1_tsep_1(X0,X1)
% 2.33/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_16,c_18]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_162,plain,
% 2.33/1.00      ( v1_tsep_1(X0,X1)
% 2.33/1.00      | ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_161]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_19,negated_conjecture,
% 2.33/1.00      ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_148,negated_conjecture,
% 2.33/1.00      ( ~ v1_tsep_1(sK3,k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_19,c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_306,plain,
% 2.33/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.33/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | k8_tmap_1(sK1,sK2) != X1
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_162,c_148]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_307,plain,
% 2.33/1.00      ( ~ m1_pre_topc(sK3,k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_306]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_309,plain,
% 2.33/1.00      ( ~ v3_pre_topc(u1_struct_0(sK3),k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_307,c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_328,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | k8_tmap_1(sK1,sK2) != X1
% 2.33/1.00      | u1_struct_0(sK3) != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_309]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_329,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(k8_tmap_1(sK1,sK2)))
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_349,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | v2_struct_0(X1)
% 2.33/1.00      | ~ v2_pre_topc(X1)
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(X1)
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | u1_struct_0(sK3) != X0
% 2.33/1.00      | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X1,X0) ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_329]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_350,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1051,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
% 2.33/1.00      inference(backward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_903,c_350]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1057,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK1,sK2))))
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
% 2.33/1.00      inference(backward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_934,c_1051]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1063,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | v2_struct_0(X0)
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | u1_pre_topc(k8_tmap_1(sK1,sK2)) != k5_tmap_1(X0,u1_struct_0(sK3)) ),
% 2.33/1.00      inference(backward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_941,c_1057]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1418,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.00      | ~ v2_pre_topc(X0)
% 2.33/1.00      | ~ l1_pre_topc(X0)
% 2.33/1.00      | k5_tmap_1(X0,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | sK1 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1063]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1419,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | ~ v2_pre_topc(sK1)
% 2.33/1.00      | ~ l1_pre_topc(sK1)
% 2.33/1.00      | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_1418]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1421,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1419,c_25,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2500,plain,
% 2.33/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.33/1.00      | k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_1421]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3438,plain,
% 2.33/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.33/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2500]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3588,plain,
% 2.33/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK3)) != u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.33/1.00      inference(forward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3438,c_3485]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,[status(thm)],[c_4939,c_3588]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.009
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.011
% 2.33/1.00  total_time:                             0.128
% 2.33/1.00  num_of_symbols:                         64
% 2.33/1.00  num_of_terms:                           2336
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          13
% 2.33/1.00  num_of_split_atoms:                     10
% 2.33/1.00  num_of_reused_defs:                     3
% 2.33/1.00  num_eq_ax_congr_red:                    8
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        4
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        0
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       189
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        100
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        9
% 2.33/1.00  pred_elim:                              6
% 2.33/1.00  pred_elim_cl:                           -28
% 2.33/1.00  pred_elim_cycles:                       8
% 2.33/1.00  merged_defs:                            0
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          0
% 2.33/1.00  prep_cycles:                            3
% 2.33/1.00  pred_elim_time:                         0.033
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                67
% 2.33/1.00  conjectures:                            3
% 2.33/1.00  epr:                                    9
% 2.33/1.00  horn:                                   47
% 2.33/1.00  ground:                                 41
% 2.33/1.00  unary:                                  8
% 2.33/1.00  binary:                                 11
% 2.33/1.00  lits:                                   196
% 2.33/1.00  lits_eq:                                90
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                0
% 2.33/1.00  fd_pseudo_cond:                         0
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      23
% 2.33/1.00  prop_fast_solver_calls:                 1867
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1164
% 2.33/1.00  prop_preprocess_simplified:             4912
% 2.33/1.00  prop_fo_subsumed:                       102
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    279
% 2.33/1.00  inst_num_in_passive:                    1
% 2.33/1.00  inst_num_in_active:                     204
% 2.33/1.00  inst_num_in_unprocessed:                74
% 2.33/1.00  inst_num_of_loops:                      210
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          2
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      44
% 2.33/1.00  inst_num_of_non_proper_insts:           211
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       192
% 2.33/1.00  res_forward_subset_subsumed:            77
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  0
% 2.33/1.00  res_forward_subsumption_resolution:     12
% 2.33/1.00  res_backward_subsumption_resolution:    18
% 2.33/1.00  res_clause_to_clause_subsumption:       245
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      58
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     71
% 2.33/1.00  sup_num_in_active:                      41
% 2.33/1.00  sup_num_in_passive:                     30
% 2.33/1.00  sup_num_of_loops:                       41
% 2.33/1.00  sup_fw_superposition:                   9
% 2.33/1.00  sup_bw_superposition:                   1
% 2.33/1.00  sup_immediate_simplified:               5
% 2.33/1.00  sup_given_eliminated:                   0
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    7
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 1
% 2.33/1.00  sim_bw_subset_subsumed:                 0
% 2.33/1.00  sim_fw_subsumed:                        0
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 1
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      0
% 2.33/1.00  sim_eq_tautology_del:                   0
% 2.33/1.00  sim_eq_res_simp:                        0
% 2.33/1.00  sim_fw_demodulated:                     0
% 2.33/1.00  sim_bw_demodulated:                     1
% 2.33/1.00  sim_light_normalised:                   23
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
