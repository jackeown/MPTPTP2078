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
% DateTime   : Thu Dec  3 12:24:09 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  205 (3906 expanded)
%              Number of clauses        :  132 ( 904 expanded)
%              Number of leaves         :   20 (1223 expanded)
%              Depth                    :   30
%              Number of atoms          : 1041 (23311 expanded)
%              Number of equality atoms :  305 (1455 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4)
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2)
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f46,f45,f44])).

fof(f74,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f76,plain,(
    ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_742,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_743,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_745,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_26])).

cnf(c_1699,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_745])).

cnf(c_2091,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_1123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1122])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1127,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1123,c_28,c_26])).

cnf(c_1689,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0_57) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1127])).

cnf(c_2099,plain,
    ( k7_tmap_1(sK2,X0_57) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1689])).

cnf(c_2398,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_2091,c_2099])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_194,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_21,c_17,c_16,c_15])).

cnf(c_195,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_726,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_24])).

cnf(c_727,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_28,c_27,c_26])).

cnf(c_1701,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_729])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1104,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1104])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_28,c_26])).

cnf(c_1690,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))))) ),
    inference(subtyping,[status(esa)],[c_1109])).

cnf(c_2098,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1690])).

cnf(c_2479,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_2098])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_755,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_756,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_758,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_28,c_27,c_26,c_25])).

cnf(c_1698,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_2480,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2479,c_1698])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_744,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_2538,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2480,c_31,c_744])).

cnf(c_2832,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2398,c_2538])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_904,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_905,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_909,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_28,c_27,c_26])).

cnf(c_910,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_1696,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0_57)
    | sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_57 ),
    inference(subtyping,[status(esa)],[c_910])).

cnf(c_2093,plain,
    ( sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_57
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_2169,plain,
    ( sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_57
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2093,c_1698])).

cnf(c_2999,plain,
    ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_2169])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1086])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1087,c_28,c_26])).

cnf(c_1691,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_57)) ),
    inference(subtyping,[status(esa)],[c_1091])).

cnf(c_2097,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_2363,plain,
    ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_2097])).

cnf(c_2831,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2398,c_2363])).

cnf(c_13,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1047,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_1048,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1047])).

cnf(c_1052,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1048,c_28,c_26])).

cnf(c_1693,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1052])).

cnf(c_2095,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_2357,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_2095])).

cnf(c_2358,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2357,c_1698])).

cnf(c_2471,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_31,c_744])).

cnf(c_2833,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2398,c_2471])).

cnf(c_3096,plain,
    ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2999,c_2831,c_2833])).

cnf(c_2,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_699,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_700,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_28,c_27,c_26])).

cnf(c_705,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_704])).

cnf(c_998,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | X6 != X3
    | k9_tmap_1(sK2,sK3) = X6
    | k7_tmap_1(sK2,sK1(sK2,sK3,X6)) != X3
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X6))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X5
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_705])).

cnf(c_999,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = X1
    | k7_tmap_1(sK2,sK1(sK2,sK3,X1)) != X1 ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1694,plain,
    ( ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))
    | ~ v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X1_57)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = X1_57
    | k7_tmap_1(sK2,sK1(sK2,sK3,X1_57)) != X1_57 ),
    inference(subtyping,[status(esa)],[c_999])).

cnf(c_2094,plain,
    ( k9_tmap_1(sK2,sK3) = X0_57
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
    | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1694])).

cnf(c_2191,plain,
    ( k9_tmap_1(sK2,sK3) = X0_57
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
    | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2094,c_1698])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_349,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1231,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_26])).

cnf(c_1232,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1231])).

cnf(c_97,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_100,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1234,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1232,c_28,c_26,c_97,c_100])).

cnf(c_1685,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1234])).

cnf(c_2103,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_2202,plain,
    ( k9_tmap_1(sK2,sK3) = X0_57
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
    | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2191,c_2103])).

cnf(c_3100,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3096,c_2202])).

cnf(c_3101,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3100,c_2398])).

cnf(c_3102,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3101])).

cnf(c_1706,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_1749,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21])).

cnf(c_178,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_367,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK2,sK3)
    | sK4 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_22])).

cnf(c_368,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_372,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_25,c_23])).

cnf(c_373,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_931,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_373])).

cnf(c_932,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_375,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_934,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_28,c_27,c_26,c_24,c_375,c_727])).

cnf(c_1695,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(subtyping,[status(esa)],[c_934])).

cnf(c_2264,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_1728,plain,
    ( k2_tmap_1(X0_56,X1_56,X0_57,X2_56) = k2_tmap_1(X3_56,X4_56,X1_57,X5_56)
    | X0_57 != X1_57
    | X0_56 != X3_56
    | X1_56 != X4_56
    | X2_56 != X5_56 ),
    theory(equality)).

cnf(c_2293,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_2341,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_1711,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_2400,plain,
    ( k9_tmap_1(sK2,sK3) != X0_57
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X0_57
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_3469,plain,
    ( k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_3548,plain,
    ( v1_funct_1(X0_57) != iProver_top
    | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3102,c_26,c_743,c_1749,c_1701,c_1695,c_2264,c_2293,c_2341,c_2831,c_2832,c_2833,c_3469])).

cnf(c_3549,plain,
    ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3548])).

cnf(c_2683,plain,
    ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_2169])).

cnf(c_2267,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_2268,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_3424,plain,
    ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2683,c_31,c_744,c_1749,c_1701,c_1695,c_2268,c_2293,c_2341,c_2358])).

cnf(c_3426,plain,
    ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3424,c_2398])).

cnf(c_3554,plain,
    ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3549,c_1698,c_1701,c_3426])).

cnf(c_3559,plain,
    ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3554,c_2103])).

cnf(c_3563,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_3559])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3563,c_2833,c_2831])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.31/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/0.98  
% 2.31/0.98  ------  iProver source info
% 2.31/0.98  
% 2.31/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.31/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/0.98  git: non_committed_changes: false
% 2.31/0.98  git: last_make_outside_of_git: false
% 2.31/0.98  
% 2.31/0.98  ------ 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options
% 2.31/0.98  
% 2.31/0.98  --out_options                           all
% 2.31/0.98  --tptp_safe_out                         true
% 2.31/0.98  --problem_path                          ""
% 2.31/0.98  --include_path                          ""
% 2.31/0.98  --clausifier                            res/vclausify_rel
% 2.31/0.98  --clausifier_options                    --mode clausify
% 2.31/0.98  --stdin                                 false
% 2.31/0.98  --stats_out                             all
% 2.31/0.98  
% 2.31/0.98  ------ General Options
% 2.31/0.98  
% 2.31/0.98  --fof                                   false
% 2.31/0.98  --time_out_real                         305.
% 2.31/0.98  --time_out_virtual                      -1.
% 2.31/0.98  --symbol_type_check                     false
% 2.31/0.98  --clausify_out                          false
% 2.31/0.98  --sig_cnt_out                           false
% 2.31/0.98  --trig_cnt_out                          false
% 2.31/0.98  --trig_cnt_out_tolerance                1.
% 2.31/0.98  --trig_cnt_out_sk_spl                   false
% 2.31/0.98  --abstr_cl_out                          false
% 2.31/0.98  
% 2.31/0.98  ------ Global Options
% 2.31/0.98  
% 2.31/0.98  --schedule                              default
% 2.31/0.98  --add_important_lit                     false
% 2.31/0.98  --prop_solver_per_cl                    1000
% 2.31/0.98  --min_unsat_core                        false
% 2.31/0.98  --soft_assumptions                      false
% 2.31/0.98  --soft_lemma_size                       3
% 2.31/0.98  --prop_impl_unit_size                   0
% 2.31/0.98  --prop_impl_unit                        []
% 2.31/0.98  --share_sel_clauses                     true
% 2.31/0.98  --reset_solvers                         false
% 2.31/0.98  --bc_imp_inh                            [conj_cone]
% 2.31/0.98  --conj_cone_tolerance                   3.
% 2.31/0.98  --extra_neg_conj                        none
% 2.31/0.98  --large_theory_mode                     true
% 2.31/0.98  --prolific_symb_bound                   200
% 2.31/0.98  --lt_threshold                          2000
% 2.31/0.98  --clause_weak_htbl                      true
% 2.31/0.98  --gc_record_bc_elim                     false
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing Options
% 2.31/0.98  
% 2.31/0.98  --preprocessing_flag                    true
% 2.31/0.98  --time_out_prep_mult                    0.1
% 2.31/0.98  --splitting_mode                        input
% 2.31/0.98  --splitting_grd                         true
% 2.31/0.98  --splitting_cvd                         false
% 2.31/0.98  --splitting_cvd_svl                     false
% 2.31/0.98  --splitting_nvd                         32
% 2.31/0.98  --sub_typing                            true
% 2.31/0.98  --prep_gs_sim                           true
% 2.31/0.98  --prep_unflatten                        true
% 2.31/0.98  --prep_res_sim                          true
% 2.31/0.98  --prep_upred                            true
% 2.31/0.98  --prep_sem_filter                       exhaustive
% 2.31/0.98  --prep_sem_filter_out                   false
% 2.31/0.98  --pred_elim                             true
% 2.31/0.98  --res_sim_input                         true
% 2.31/0.98  --eq_ax_congr_red                       true
% 2.31/0.98  --pure_diseq_elim                       true
% 2.31/0.98  --brand_transform                       false
% 2.31/0.98  --non_eq_to_eq                          false
% 2.31/0.98  --prep_def_merge                        true
% 2.31/0.98  --prep_def_merge_prop_impl              false
% 2.31/0.98  --prep_def_merge_mbd                    true
% 2.31/0.98  --prep_def_merge_tr_red                 false
% 2.31/0.98  --prep_def_merge_tr_cl                  false
% 2.31/0.98  --smt_preprocessing                     true
% 2.31/0.98  --smt_ac_axioms                         fast
% 2.31/0.98  --preprocessed_out                      false
% 2.31/0.98  --preprocessed_stats                    false
% 2.31/0.98  
% 2.31/0.98  ------ Abstraction refinement Options
% 2.31/0.98  
% 2.31/0.98  --abstr_ref                             []
% 2.31/0.98  --abstr_ref_prep                        false
% 2.31/0.98  --abstr_ref_until_sat                   false
% 2.31/0.98  --abstr_ref_sig_restrict                funpre
% 2.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.98  --abstr_ref_under                       []
% 2.31/0.98  
% 2.31/0.98  ------ SAT Options
% 2.31/0.98  
% 2.31/0.98  --sat_mode                              false
% 2.31/0.98  --sat_fm_restart_options                ""
% 2.31/0.98  --sat_gr_def                            false
% 2.31/0.98  --sat_epr_types                         true
% 2.31/0.98  --sat_non_cyclic_types                  false
% 2.31/0.98  --sat_finite_models                     false
% 2.31/0.98  --sat_fm_lemmas                         false
% 2.31/0.98  --sat_fm_prep                           false
% 2.31/0.98  --sat_fm_uc_incr                        true
% 2.31/0.98  --sat_out_model                         small
% 2.31/0.98  --sat_out_clauses                       false
% 2.31/0.98  
% 2.31/0.98  ------ QBF Options
% 2.31/0.98  
% 2.31/0.98  --qbf_mode                              false
% 2.31/0.98  --qbf_elim_univ                         false
% 2.31/0.98  --qbf_dom_inst                          none
% 2.31/0.98  --qbf_dom_pre_inst                      false
% 2.31/0.98  --qbf_sk_in                             false
% 2.31/0.98  --qbf_pred_elim                         true
% 2.31/0.98  --qbf_split                             512
% 2.31/0.98  
% 2.31/0.98  ------ BMC1 Options
% 2.31/0.98  
% 2.31/0.98  --bmc1_incremental                      false
% 2.31/0.98  --bmc1_axioms                           reachable_all
% 2.31/0.98  --bmc1_min_bound                        0
% 2.31/0.98  --bmc1_max_bound                        -1
% 2.31/0.98  --bmc1_max_bound_default                -1
% 2.31/0.98  --bmc1_symbol_reachability              true
% 2.31/0.98  --bmc1_property_lemmas                  false
% 2.31/0.98  --bmc1_k_induction                      false
% 2.31/0.98  --bmc1_non_equiv_states                 false
% 2.31/0.98  --bmc1_deadlock                         false
% 2.31/0.98  --bmc1_ucm                              false
% 2.31/0.98  --bmc1_add_unsat_core                   none
% 2.31/0.98  --bmc1_unsat_core_children              false
% 2.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.98  --bmc1_out_stat                         full
% 2.31/0.98  --bmc1_ground_init                      false
% 2.31/0.98  --bmc1_pre_inst_next_state              false
% 2.31/0.98  --bmc1_pre_inst_state                   false
% 2.31/0.98  --bmc1_pre_inst_reach_state             false
% 2.31/0.98  --bmc1_out_unsat_core                   false
% 2.31/0.98  --bmc1_aig_witness_out                  false
% 2.31/0.98  --bmc1_verbose                          false
% 2.31/0.98  --bmc1_dump_clauses_tptp                false
% 2.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.98  --bmc1_dump_file                        -
% 2.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.98  --bmc1_ucm_extend_mode                  1
% 2.31/0.98  --bmc1_ucm_init_mode                    2
% 2.31/0.98  --bmc1_ucm_cone_mode                    none
% 2.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.98  --bmc1_ucm_relax_model                  4
% 2.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.98  --bmc1_ucm_layered_model                none
% 2.31/0.98  --bmc1_ucm_max_lemma_size               10
% 2.31/0.98  
% 2.31/0.98  ------ AIG Options
% 2.31/0.98  
% 2.31/0.98  --aig_mode                              false
% 2.31/0.98  
% 2.31/0.98  ------ Instantiation Options
% 2.31/0.98  
% 2.31/0.98  --instantiation_flag                    true
% 2.31/0.98  --inst_sos_flag                         false
% 2.31/0.98  --inst_sos_phase                        true
% 2.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel_side                     num_symb
% 2.31/0.98  --inst_solver_per_active                1400
% 2.31/0.98  --inst_solver_calls_frac                1.
% 2.31/0.98  --inst_passive_queue_type               priority_queues
% 2.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.98  --inst_passive_queues_freq              [25;2]
% 2.31/0.98  --inst_dismatching                      true
% 2.31/0.98  --inst_eager_unprocessed_to_passive     true
% 2.31/0.98  --inst_prop_sim_given                   true
% 2.31/0.98  --inst_prop_sim_new                     false
% 2.31/0.98  --inst_subs_new                         false
% 2.31/0.98  --inst_eq_res_simp                      false
% 2.31/0.98  --inst_subs_given                       false
% 2.31/0.98  --inst_orphan_elimination               true
% 2.31/0.98  --inst_learning_loop_flag               true
% 2.31/0.98  --inst_learning_start                   3000
% 2.31/0.98  --inst_learning_factor                  2
% 2.31/0.98  --inst_start_prop_sim_after_learn       3
% 2.31/0.98  --inst_sel_renew                        solver
% 2.31/0.98  --inst_lit_activity_flag                true
% 2.31/0.98  --inst_restr_to_given                   false
% 2.31/0.98  --inst_activity_threshold               500
% 2.31/0.98  --inst_out_proof                        true
% 2.31/0.98  
% 2.31/0.98  ------ Resolution Options
% 2.31/0.98  
% 2.31/0.98  --resolution_flag                       true
% 2.31/0.98  --res_lit_sel                           adaptive
% 2.31/0.98  --res_lit_sel_side                      none
% 2.31/0.98  --res_ordering                          kbo
% 2.31/0.98  --res_to_prop_solver                    active
% 2.31/0.98  --res_prop_simpl_new                    false
% 2.31/0.98  --res_prop_simpl_given                  true
% 2.31/0.98  --res_passive_queue_type                priority_queues
% 2.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.99  --res_passive_queues_freq               [15;5]
% 2.31/0.99  --res_forward_subs                      full
% 2.31/0.99  --res_backward_subs                     full
% 2.31/0.99  --res_forward_subs_resolution           true
% 2.31/0.99  --res_backward_subs_resolution          true
% 2.31/0.99  --res_orphan_elimination                true
% 2.31/0.99  --res_time_limit                        2.
% 2.31/0.99  --res_out_proof                         true
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Options
% 2.31/0.99  
% 2.31/0.99  --superposition_flag                    true
% 2.31/0.99  --sup_passive_queue_type                priority_queues
% 2.31/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.99  --demod_completeness_check              fast
% 2.31/0.99  --demod_use_ground                      true
% 2.31/0.99  --sup_to_prop_solver                    passive
% 2.31/0.99  --sup_prop_simpl_new                    true
% 2.31/0.99  --sup_prop_simpl_given                  true
% 2.31/0.99  --sup_fun_splitting                     false
% 2.31/0.99  --sup_smt_interval                      50000
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Simplification Setup
% 2.31/0.99  
% 2.31/0.99  --sup_indices_passive                   []
% 2.31/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_full_bw                           [BwDemod]
% 2.31/0.99  --sup_immed_triv                        [TrivRules]
% 2.31/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_immed_bw_main                     []
% 2.31/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  
% 2.31/0.99  ------ Combination Options
% 2.31/0.99  
% 2.31/0.99  --comb_res_mult                         3
% 2.31/0.99  --comb_sup_mult                         2
% 2.31/0.99  --comb_inst_mult                        10
% 2.31/0.99  
% 2.31/0.99  ------ Debug Options
% 2.31/0.99  
% 2.31/0.99  --dbg_backtrace                         false
% 2.31/0.99  --dbg_dump_prop_clauses                 false
% 2.31/0.99  --dbg_dump_prop_clauses_file            -
% 2.31/0.99  --dbg_out_stat                          false
% 2.31/0.99  ------ Parsing...
% 2.31/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/0.99  ------ Proving...
% 2.31/0.99  ------ Problem Properties 
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  clauses                                 21
% 2.31/0.99  conjectures                             3
% 2.31/0.99  EPR                                     2
% 2.31/0.99  Horn                                    14
% 2.31/0.99  unary                                   9
% 2.31/0.99  binary                                  5
% 2.31/0.99  lits                                    51
% 2.31/0.99  lits eq                                 11
% 2.31/0.99  fd_pure                                 0
% 2.31/0.99  fd_pseudo                               0
% 2.31/0.99  fd_cond                                 3
% 2.31/0.99  fd_pseudo_cond                          0
% 2.31/0.99  AC symbols                              0
% 2.31/0.99  
% 2.31/0.99  ------ Schedule dynamic 5 is on 
% 2.31/0.99  
% 2.31/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  ------ 
% 2.31/0.99  Current options:
% 2.31/0.99  ------ 
% 2.31/0.99  
% 2.31/0.99  ------ Input Options
% 2.31/0.99  
% 2.31/0.99  --out_options                           all
% 2.31/0.99  --tptp_safe_out                         true
% 2.31/0.99  --problem_path                          ""
% 2.31/0.99  --include_path                          ""
% 2.31/0.99  --clausifier                            res/vclausify_rel
% 2.31/0.99  --clausifier_options                    --mode clausify
% 2.31/0.99  --stdin                                 false
% 2.31/0.99  --stats_out                             all
% 2.31/0.99  
% 2.31/0.99  ------ General Options
% 2.31/0.99  
% 2.31/0.99  --fof                                   false
% 2.31/0.99  --time_out_real                         305.
% 2.31/0.99  --time_out_virtual                      -1.
% 2.31/0.99  --symbol_type_check                     false
% 2.31/0.99  --clausify_out                          false
% 2.31/0.99  --sig_cnt_out                           false
% 2.31/0.99  --trig_cnt_out                          false
% 2.31/0.99  --trig_cnt_out_tolerance                1.
% 2.31/0.99  --trig_cnt_out_sk_spl                   false
% 2.31/0.99  --abstr_cl_out                          false
% 2.31/0.99  
% 2.31/0.99  ------ Global Options
% 2.31/0.99  
% 2.31/0.99  --schedule                              default
% 2.31/0.99  --add_important_lit                     false
% 2.31/0.99  --prop_solver_per_cl                    1000
% 2.31/0.99  --min_unsat_core                        false
% 2.31/0.99  --soft_assumptions                      false
% 2.31/0.99  --soft_lemma_size                       3
% 2.31/0.99  --prop_impl_unit_size                   0
% 2.31/0.99  --prop_impl_unit                        []
% 2.31/0.99  --share_sel_clauses                     true
% 2.31/0.99  --reset_solvers                         false
% 2.31/0.99  --bc_imp_inh                            [conj_cone]
% 2.31/0.99  --conj_cone_tolerance                   3.
% 2.31/0.99  --extra_neg_conj                        none
% 2.31/0.99  --large_theory_mode                     true
% 2.31/0.99  --prolific_symb_bound                   200
% 2.31/0.99  --lt_threshold                          2000
% 2.31/0.99  --clause_weak_htbl                      true
% 2.31/0.99  --gc_record_bc_elim                     false
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing Options
% 2.31/0.99  
% 2.31/0.99  --preprocessing_flag                    true
% 2.31/0.99  --time_out_prep_mult                    0.1
% 2.31/0.99  --splitting_mode                        input
% 2.31/0.99  --splitting_grd                         true
% 2.31/0.99  --splitting_cvd                         false
% 2.31/0.99  --splitting_cvd_svl                     false
% 2.31/0.99  --splitting_nvd                         32
% 2.31/0.99  --sub_typing                            true
% 2.31/0.99  --prep_gs_sim                           true
% 2.31/0.99  --prep_unflatten                        true
% 2.31/0.99  --prep_res_sim                          true
% 2.31/0.99  --prep_upred                            true
% 2.31/0.99  --prep_sem_filter                       exhaustive
% 2.31/0.99  --prep_sem_filter_out                   false
% 2.31/0.99  --pred_elim                             true
% 2.31/0.99  --res_sim_input                         true
% 2.31/0.99  --eq_ax_congr_red                       true
% 2.31/0.99  --pure_diseq_elim                       true
% 2.31/0.99  --brand_transform                       false
% 2.31/0.99  --non_eq_to_eq                          false
% 2.31/0.99  --prep_def_merge                        true
% 2.31/0.99  --prep_def_merge_prop_impl              false
% 2.31/0.99  --prep_def_merge_mbd                    true
% 2.31/0.99  --prep_def_merge_tr_red                 false
% 2.31/0.99  --prep_def_merge_tr_cl                  false
% 2.31/0.99  --smt_preprocessing                     true
% 2.31/0.99  --smt_ac_axioms                         fast
% 2.31/0.99  --preprocessed_out                      false
% 2.31/0.99  --preprocessed_stats                    false
% 2.31/0.99  
% 2.31/0.99  ------ Abstraction refinement Options
% 2.31/0.99  
% 2.31/0.99  --abstr_ref                             []
% 2.31/0.99  --abstr_ref_prep                        false
% 2.31/0.99  --abstr_ref_until_sat                   false
% 2.31/0.99  --abstr_ref_sig_restrict                funpre
% 2.31/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.99  --abstr_ref_under                       []
% 2.31/0.99  
% 2.31/0.99  ------ SAT Options
% 2.31/0.99  
% 2.31/0.99  --sat_mode                              false
% 2.31/0.99  --sat_fm_restart_options                ""
% 2.31/0.99  --sat_gr_def                            false
% 2.31/0.99  --sat_epr_types                         true
% 2.31/0.99  --sat_non_cyclic_types                  false
% 2.31/0.99  --sat_finite_models                     false
% 2.31/0.99  --sat_fm_lemmas                         false
% 2.31/0.99  --sat_fm_prep                           false
% 2.31/0.99  --sat_fm_uc_incr                        true
% 2.31/0.99  --sat_out_model                         small
% 2.31/0.99  --sat_out_clauses                       false
% 2.31/0.99  
% 2.31/0.99  ------ QBF Options
% 2.31/0.99  
% 2.31/0.99  --qbf_mode                              false
% 2.31/0.99  --qbf_elim_univ                         false
% 2.31/0.99  --qbf_dom_inst                          none
% 2.31/0.99  --qbf_dom_pre_inst                      false
% 2.31/0.99  --qbf_sk_in                             false
% 2.31/0.99  --qbf_pred_elim                         true
% 2.31/0.99  --qbf_split                             512
% 2.31/0.99  
% 2.31/0.99  ------ BMC1 Options
% 2.31/0.99  
% 2.31/0.99  --bmc1_incremental                      false
% 2.31/0.99  --bmc1_axioms                           reachable_all
% 2.31/0.99  --bmc1_min_bound                        0
% 2.31/0.99  --bmc1_max_bound                        -1
% 2.31/0.99  --bmc1_max_bound_default                -1
% 2.31/0.99  --bmc1_symbol_reachability              true
% 2.31/0.99  --bmc1_property_lemmas                  false
% 2.31/0.99  --bmc1_k_induction                      false
% 2.31/0.99  --bmc1_non_equiv_states                 false
% 2.31/0.99  --bmc1_deadlock                         false
% 2.31/0.99  --bmc1_ucm                              false
% 2.31/0.99  --bmc1_add_unsat_core                   none
% 2.31/0.99  --bmc1_unsat_core_children              false
% 2.31/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.99  --bmc1_out_stat                         full
% 2.31/0.99  --bmc1_ground_init                      false
% 2.31/0.99  --bmc1_pre_inst_next_state              false
% 2.31/0.99  --bmc1_pre_inst_state                   false
% 2.31/0.99  --bmc1_pre_inst_reach_state             false
% 2.31/0.99  --bmc1_out_unsat_core                   false
% 2.31/0.99  --bmc1_aig_witness_out                  false
% 2.31/0.99  --bmc1_verbose                          false
% 2.31/0.99  --bmc1_dump_clauses_tptp                false
% 2.31/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.99  --bmc1_dump_file                        -
% 2.31/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.99  --bmc1_ucm_extend_mode                  1
% 2.31/0.99  --bmc1_ucm_init_mode                    2
% 2.31/0.99  --bmc1_ucm_cone_mode                    none
% 2.31/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.99  --bmc1_ucm_relax_model                  4
% 2.31/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.99  --bmc1_ucm_layered_model                none
% 2.31/0.99  --bmc1_ucm_max_lemma_size               10
% 2.31/0.99  
% 2.31/0.99  ------ AIG Options
% 2.31/0.99  
% 2.31/0.99  --aig_mode                              false
% 2.31/0.99  
% 2.31/0.99  ------ Instantiation Options
% 2.31/0.99  
% 2.31/0.99  --instantiation_flag                    true
% 2.31/0.99  --inst_sos_flag                         false
% 2.31/0.99  --inst_sos_phase                        true
% 2.31/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.99  --inst_lit_sel_side                     none
% 2.31/0.99  --inst_solver_per_active                1400
% 2.31/0.99  --inst_solver_calls_frac                1.
% 2.31/0.99  --inst_passive_queue_type               priority_queues
% 2.31/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.99  --inst_passive_queues_freq              [25;2]
% 2.31/0.99  --inst_dismatching                      true
% 2.31/0.99  --inst_eager_unprocessed_to_passive     true
% 2.31/0.99  --inst_prop_sim_given                   true
% 2.31/0.99  --inst_prop_sim_new                     false
% 2.31/0.99  --inst_subs_new                         false
% 2.31/0.99  --inst_eq_res_simp                      false
% 2.31/0.99  --inst_subs_given                       false
% 2.31/0.99  --inst_orphan_elimination               true
% 2.31/0.99  --inst_learning_loop_flag               true
% 2.31/0.99  --inst_learning_start                   3000
% 2.31/0.99  --inst_learning_factor                  2
% 2.31/0.99  --inst_start_prop_sim_after_learn       3
% 2.31/0.99  --inst_sel_renew                        solver
% 2.31/0.99  --inst_lit_activity_flag                true
% 2.31/0.99  --inst_restr_to_given                   false
% 2.31/0.99  --inst_activity_threshold               500
% 2.31/0.99  --inst_out_proof                        true
% 2.31/0.99  
% 2.31/0.99  ------ Resolution Options
% 2.31/0.99  
% 2.31/0.99  --resolution_flag                       false
% 2.31/0.99  --res_lit_sel                           adaptive
% 2.31/0.99  --res_lit_sel_side                      none
% 2.31/0.99  --res_ordering                          kbo
% 2.31/0.99  --res_to_prop_solver                    active
% 2.31/0.99  --res_prop_simpl_new                    false
% 2.31/0.99  --res_prop_simpl_given                  true
% 2.31/0.99  --res_passive_queue_type                priority_queues
% 2.31/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.99  --res_passive_queues_freq               [15;5]
% 2.31/0.99  --res_forward_subs                      full
% 2.31/0.99  --res_backward_subs                     full
% 2.31/0.99  --res_forward_subs_resolution           true
% 2.31/0.99  --res_backward_subs_resolution          true
% 2.31/0.99  --res_orphan_elimination                true
% 2.31/0.99  --res_time_limit                        2.
% 2.31/0.99  --res_out_proof                         true
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Options
% 2.31/0.99  
% 2.31/0.99  --superposition_flag                    true
% 2.31/0.99  --sup_passive_queue_type                priority_queues
% 2.31/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.99  --demod_completeness_check              fast
% 2.31/0.99  --demod_use_ground                      true
% 2.31/0.99  --sup_to_prop_solver                    passive
% 2.31/0.99  --sup_prop_simpl_new                    true
% 2.31/0.99  --sup_prop_simpl_given                  true
% 2.31/0.99  --sup_fun_splitting                     false
% 2.31/0.99  --sup_smt_interval                      50000
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Simplification Setup
% 2.31/0.99  
% 2.31/0.99  --sup_indices_passive                   []
% 2.31/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_full_bw                           [BwDemod]
% 2.31/0.99  --sup_immed_triv                        [TrivRules]
% 2.31/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_immed_bw_main                     []
% 2.31/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  
% 2.31/0.99  ------ Combination Options
% 2.31/0.99  
% 2.31/0.99  --comb_res_mult                         3
% 2.31/0.99  --comb_sup_mult                         2
% 2.31/0.99  --comb_inst_mult                        10
% 2.31/0.99  
% 2.31/0.99  ------ Debug Options
% 2.31/0.99  
% 2.31/0.99  --dbg_backtrace                         false
% 2.31/0.99  --dbg_dump_prop_clauses                 false
% 2.31/0.99  --dbg_dump_prop_clauses_file            -
% 2.31/0.99  --dbg_out_stat                          false
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  ------ Proving...
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  % SZS status Theorem for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  fof(f11,axiom,(
% 2.31/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f33,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.31/0.99    inference(ennf_transformation,[],[f11])).
% 2.31/0.99  
% 2.31/0.99  fof(f69,plain,(
% 2.31/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f33])).
% 2.31/0.99  
% 2.31/0.99  fof(f12,conjecture,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f13,negated_conjecture,(
% 2.31/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 2.31/0.99    inference(negated_conjecture,[],[f12])).
% 2.31/0.99  
% 2.31/0.99  fof(f34,plain,(
% 2.31/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f13])).
% 2.31/0.99  
% 2.31/0.99  fof(f35,plain,(
% 2.31/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f34])).
% 2.31/0.99  
% 2.31/0.99  fof(f46,plain,(
% 2.31/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f45,plain,(
% 2.31/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f44,plain,(
% 2.31/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f47,plain,(
% 2.31/0.99    ((~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f46,f45,f44])).
% 2.31/0.99  
% 2.31/0.99  fof(f74,plain,(
% 2.31/0.99    m1_pre_topc(sK3,sK2)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f72,plain,(
% 2.31/0.99    l1_pre_topc(sK2)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f4,axiom,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f19,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f4])).
% 2.31/0.99  
% 2.31/0.99  fof(f20,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f19])).
% 2.31/0.99  
% 2.31/0.99  fof(f51,plain,(
% 2.31/0.99    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f20])).
% 2.31/0.99  
% 2.31/0.99  fof(f71,plain,(
% 2.31/0.99    v2_pre_topc(sK2)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f70,plain,(
% 2.31/0.99    ~v2_struct_0(sK2)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f5,axiom,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f21,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f5])).
% 2.31/0.99  
% 2.31/0.99  fof(f22,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f21])).
% 2.31/0.99  
% 2.31/0.99  fof(f36,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(nnf_transformation,[],[f22])).
% 2.31/0.99  
% 2.31/0.99  fof(f37,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(rectify,[],[f36])).
% 2.31/0.99  
% 2.31/0.99  fof(f38,plain,(
% 2.31/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f39,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.31/0.99  
% 2.31/0.99  fof(f52,plain,(
% 2.31/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f39])).
% 2.31/0.99  
% 2.31/0.99  fof(f77,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(equality_resolution,[],[f52])).
% 2.31/0.99  
% 2.31/0.99  fof(f78,plain,(
% 2.31/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(equality_resolution,[],[f77])).
% 2.31/0.99  
% 2.31/0.99  fof(f8,axiom,(
% 2.31/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f27,plain,(
% 2.31/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f8])).
% 2.31/0.99  
% 2.31/0.99  fof(f28,plain,(
% 2.31/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f27])).
% 2.31/0.99  
% 2.31/0.99  fof(f63,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  fof(f64,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  fof(f65,plain,(
% 2.31/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  fof(f7,axiom,(
% 2.31/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f25,plain,(
% 2.31/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f7])).
% 2.31/0.99  
% 2.31/0.99  fof(f26,plain,(
% 2.31/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f25])).
% 2.31/0.99  
% 2.31/0.99  fof(f62,plain,(
% 2.31/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f26])).
% 2.31/0.99  
% 2.31/0.99  fof(f10,axiom,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f31,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f10])).
% 2.31/0.99  
% 2.31/0.99  fof(f32,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f31])).
% 2.31/0.99  
% 2.31/0.99  fof(f67,plain,(
% 2.31/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f32])).
% 2.31/0.99  
% 2.31/0.99  fof(f73,plain,(
% 2.31/0.99    ~v2_struct_0(sK3)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f6,axiom,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f23,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f6])).
% 2.31/0.99  
% 2.31/0.99  fof(f24,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f23])).
% 2.31/0.99  
% 2.31/0.99  fof(f40,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(nnf_transformation,[],[f24])).
% 2.31/0.99  
% 2.31/0.99  fof(f41,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(rectify,[],[f40])).
% 2.31/0.99  
% 2.31/0.99  fof(f42,plain,(
% 2.31/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f43,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 2.31/0.99  
% 2.31/0.99  fof(f58,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f43])).
% 2.31/0.99  
% 2.31/0.99  fof(f60,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f26])).
% 2.31/0.99  
% 2.31/0.99  fof(f61,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f26])).
% 2.31/0.99  
% 2.31/0.99  fof(f3,axiom,(
% 2.31/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f17,plain,(
% 2.31/0.99    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.31/0.99    inference(ennf_transformation,[],[f3])).
% 2.31/0.99  
% 2.31/0.99  fof(f18,plain,(
% 2.31/0.99    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.31/0.99    inference(flattening,[],[f17])).
% 2.31/0.99  
% 2.31/0.99  fof(f50,plain,(
% 2.31/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f18])).
% 2.31/0.99  
% 2.31/0.99  fof(f59,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f43])).
% 2.31/0.99  
% 2.31/0.99  fof(f1,axiom,(
% 2.31/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f14,plain,(
% 2.31/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.31/0.99    inference(ennf_transformation,[],[f1])).
% 2.31/0.99  
% 2.31/0.99  fof(f48,plain,(
% 2.31/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f14])).
% 2.31/0.99  
% 2.31/0.99  fof(f2,axiom,(
% 2.31/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f15,plain,(
% 2.31/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f2])).
% 2.31/0.99  
% 2.31/0.99  fof(f16,plain,(
% 2.31/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f15])).
% 2.31/0.99  
% 2.31/0.99  fof(f49,plain,(
% 2.31/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f16])).
% 2.31/0.99  
% 2.31/0.99  fof(f9,axiom,(
% 2.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f29,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.99    inference(ennf_transformation,[],[f9])).
% 2.31/0.99  
% 2.31/0.99  fof(f30,plain,(
% 2.31/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.99    inference(flattening,[],[f29])).
% 2.31/0.99  
% 2.31/0.99  fof(f66,plain,(
% 2.31/0.99    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f30])).
% 2.31/0.99  
% 2.31/0.99  fof(f81,plain,(
% 2.31/0.99    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.99    inference(equality_resolution,[],[f66])).
% 2.31/0.99  
% 2.31/0.99  fof(f76,plain,(
% 2.31/0.99    ~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  fof(f75,plain,(
% 2.31/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.31/0.99    inference(cnf_transformation,[],[f47])).
% 2.31/0.99  
% 2.31/0.99  cnf(c_21,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_24,negated_conjecture,
% 2.31/0.99      ( m1_pre_topc(sK3,sK2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_742,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | sK2 != X1
% 2.31/0.99      | sK3 != X0 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_743,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | ~ l1_pre_topc(sK2) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_742]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_26,negated_conjecture,
% 2.31/0.99      ( l1_pre_topc(sK2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_745,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_743,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1699,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_745]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2091,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.31/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_27,negated_conjecture,
% 2.31/0.99      ( v2_pre_topc(sK2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1122,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.31/0.99      | sK2 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1123,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_1122]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_28,negated_conjecture,
% 2.31/0.99      ( ~ v2_struct_0(sK2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1127,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1123,c_28,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1689,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | k7_tmap_1(sK2,X0_57) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_1127]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2099,plain,
% 2.31/0.99      ( k7_tmap_1(sK2,X0_57) = k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1689]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2398,plain,
% 2.31/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2091,c_2099]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_7,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.31/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_17,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_16,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_15,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.31/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_194,plain,
% 2.31/0.99      ( ~ l1_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_7,c_21,c_17,c_16,c_15]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_195,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_194]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_726,plain,
% 2.31/0.99      ( ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.31/0.99      | sK2 != X0
% 2.31/0.99      | sK3 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_195,c_24]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_727,plain,
% 2.31/0.99      ( ~ v2_pre_topc(sK2)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_729,plain,
% 2.31/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_727,c_28,c_27,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1701,plain,
% 2.31/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_729]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_12,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1104,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | sK2 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1105,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_1104]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1109,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1105,c_28,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1690,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))))) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_1109]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2098,plain,
% 2.31/0.99      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))))) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1690]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2479,plain,
% 2.31/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 2.31/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1701,c_2098]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_20,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_755,plain,
% 2.31/0.99      ( ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 2.31/0.99      | sK2 != X0
% 2.31/0.99      | sK3 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_756,plain,
% 2.31/0.99      ( ~ v2_pre_topc(sK2)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | v2_struct_0(sK3)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_755]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_25,negated_conjecture,
% 2.31/0.99      ( ~ v2_struct_0(sK3) ),
% 2.31/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_758,plain,
% 2.31/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_756,c_28,c_27,c_26,c_25]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1698,plain,
% 2.31/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_758]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2480,plain,
% 2.31/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 2.31/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_2479,c_1698]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_31,plain,
% 2.31/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_744,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.31/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2538,plain,
% 2.31/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2480,c_31,c_744]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2832,plain,
% 2.31/0.99      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2398,c_2538]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_9,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 2.31/0.99      | ~ m1_pre_topc(X2,X1)
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 2.31/0.99      | k9_tmap_1(X1,X2) = X0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_904,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 2.31/0.99      | k9_tmap_1(X1,X2) = X0
% 2.31/0.99      | sK2 != X1
% 2.31/0.99      | sK3 != X2 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_905,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v2_pre_topc(sK2)
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_904]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_909,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_905,c_28,c_27,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_910,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_909]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1696,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0_57)
% 2.31/0.99      | sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0_57 ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_910]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2093,plain,
% 2.31/0.99      ( sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0_57
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2169,plain,
% 2.31/0.99      ( sK1(sK2,sK3,X0_57) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0_57
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_2093,c_1698]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2999,plain,
% 2.31/0.99      ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2832,c_2169]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_14,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1086,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | sK2 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1087,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,X0))
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_1086]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1091,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,X0)) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1087,c_28,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1691,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,X0_57)) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_1091]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2097,plain,
% 2.31/0.99      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,X0_57)) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2363,plain,
% 2.31/0.99      ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2091,c_2097]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2831,plain,
% 2.31/0.99      ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2398,c_2363]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_13,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.31/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1047,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.31/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | sK2 != X0 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1048,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_1047]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1052,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1048,c_28,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1693,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57)))
% 2.31/0.99      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_1052]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2095,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_57))) = iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2357,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 2.31/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1701,c_2095]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2358,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 2.31/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_2357,c_1698]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2471,plain,
% 2.31/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2358,c_31,c_744]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2833,plain,
% 2.31/0.99      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2398,c_2471]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3096,plain,
% 2.31/0.99      ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2999,c_2831,c_2833]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2,plain,
% 2.31/0.99      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.31/0.99      | ~ v1_funct_2(X5,X2,X3)
% 2.31/0.99      | ~ v1_funct_2(X4,X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.31/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.31/0.99      | ~ v1_funct_1(X5)
% 2.31/0.99      | ~ v1_funct_1(X4)
% 2.31/0.99      | v1_xboole_0(X1)
% 2.31/0.99      | v1_xboole_0(X3) ),
% 2.31/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_8,plain,
% 2.31/0.99      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 2.31/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.31/0.99      | ~ m1_pre_topc(X1,X0)
% 2.31/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | ~ v1_funct_1(X2)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k9_tmap_1(X0,X1) = X2 ),
% 2.31/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_699,plain,
% 2.31/0.99      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 2.31/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.31/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | ~ v1_funct_1(X2)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k9_tmap_1(X0,X1) = X2
% 2.31/0.99      | sK2 != X0
% 2.31/0.99      | sK3 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_700,plain,
% 2.31/0.99      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 2.31/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v2_pre_topc(sK2)
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_699]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_704,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_700,c_28,c_27,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_705,plain,
% 2.31/0.99      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 2.31/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X0 ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_704]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_998,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.31/0.99      | ~ v1_funct_2(X3,X4,X5)
% 2.31/0.99      | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.31/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | ~ v1_funct_1(X3)
% 2.31/0.99      | ~ v1_funct_1(X6)
% 2.31/0.99      | v1_xboole_0(X5)
% 2.31/0.99      | v1_xboole_0(X2)
% 2.31/0.99      | X6 != X3
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X6
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X6)) != X3
% 2.31/0.99      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X6))) != X2
% 2.31/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X5
% 2.31/0.99      | u1_struct_0(sK2) != X1
% 2.31/0.99      | u1_struct_0(sK2) != X4 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_705]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_999,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
% 2.31/0.99      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))))
% 2.31/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0)
% 2.31/0.99      | ~ v1_funct_1(X1)
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X1
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X1)) != X1 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_998]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1694,plain,
% 2.31/0.99      ( ~ v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))
% 2.31/0.99      | ~ v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))))
% 2.31/0.99      | ~ m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.31/0.99      | ~ v1_funct_1(X0_57)
% 2.31/0.99      | ~ v1_funct_1(X1_57)
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_57))))
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.31/0.99      | k9_tmap_1(sK2,sK3) = X1_57
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X1_57)) != X1_57 ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_999]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2094,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = X0_57
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
% 2.31/0.99      | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 2.31/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 2.31/0.99      | v1_funct_1(X1_57) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1694]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2191,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = X0_57
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
% 2.31/0.99      | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_1(X1_57) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_2094,c_1698]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_0,plain,
% 2.31/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1,plain,
% 2.31/0.99      ( v2_struct_0(X0)
% 2.31/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.31/0.99      | ~ l1_struct_0(X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_349,plain,
% 2.31/0.99      ( v2_struct_0(X0)
% 2.31/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.31/0.99      | ~ l1_pre_topc(X0) ),
% 2.31/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1231,plain,
% 2.31/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_349,c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1232,plain,
% 2.31/0.99      ( v2_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_1231]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_97,plain,
% 2.31/0.99      ( v2_struct_0(sK2)
% 2.31/0.99      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.31/0.99      | ~ l1_struct_0(sK2) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_100,plain,
% 2.31/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1234,plain,
% 2.31/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1232,c_28,c_26,c_97,c_100]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1685,plain,
% 2.31/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_1234]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2103,plain,
% 2.31/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2202,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = X0_57
% 2.31/0.99      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_57)) != X0_57
% 2.31/0.99      | v1_funct_2(X1_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) != iProver_top
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_1(X1_57) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_57)))) = iProver_top ),
% 2.31/0.99      inference(forward_subsumption_resolution,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2191,c_2103]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3100,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 2.31/0.99      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 2.31/0.99      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_3096,c_2202]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3101,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 2.31/0.99      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 2.31/0.99      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_3100,c_2398]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3102,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 2.31/0.99      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 2.31/0.99      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 2.31/0.99      inference(equality_resolution_simp,[status(thm)],[c_3101]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1706,plain,( X0_56 = X0_56 ),theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1749,plain,
% 2.31/0.99      ( sK2 = sK2 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1706]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_18,plain,
% 2.31/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.31/0.99      | ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.31/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_177,plain,
% 2.31/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.31/0.99      | ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_18,c_21]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_178,plain,
% 2.31/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 2.31/0.99      | ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1) ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_177]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_22,negated_conjecture,
% 2.31/0.99      ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
% 2.31/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_367,plain,
% 2.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.31/0.99      | ~ v2_pre_topc(X1)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | v2_struct_0(X1)
% 2.31/0.99      | ~ l1_pre_topc(X1)
% 2.31/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK2,sK3)
% 2.31/0.99      | sK4 != X2
% 2.31/0.99      | sK3 != X0 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_178,c_22]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_368,plain,
% 2.31/0.99      ( ~ m1_pre_topc(sK3,X0)
% 2.31/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | v2_struct_0(sK3)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_23,negated_conjecture,
% 2.31/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.31/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_372,plain,
% 2.31/0.99      ( v2_struct_0(X0)
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | ~ m1_pre_topc(sK3,X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_368,c_25,c_23]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_373,plain,
% 2.31/0.99      ( ~ m1_pre_topc(sK3,X0)
% 2.31/0.99      | ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_931,plain,
% 2.31/0.99      ( ~ v2_pre_topc(X0)
% 2.31/0.99      | v2_struct_0(X0)
% 2.31/0.99      | ~ l1_pre_topc(X0)
% 2.31/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 2.31/0.99      | sK2 != X0
% 2.31/0.99      | sK3 != sK3 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_373]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_932,plain,
% 2.31/0.99      ( ~ v2_pre_topc(sK2)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_931]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_375,plain,
% 2.31/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 2.31/0.99      | ~ v2_pre_topc(sK2)
% 2.31/0.99      | v2_struct_0(sK2)
% 2.31/0.99      | ~ l1_pre_topc(sK2)
% 2.31/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_373]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_934,plain,
% 2.31/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_932,c_28,c_27,c_26,c_24,c_375,c_727]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1695,plain,
% 2.31/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 2.31/0.99      inference(subtyping,[status(esa)],[c_934]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2264,plain,
% 2.31/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1689]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1728,plain,
% 2.31/0.99      ( k2_tmap_1(X0_56,X1_56,X0_57,X2_56) = k2_tmap_1(X3_56,X4_56,X1_57,X5_56)
% 2.31/0.99      | X0_57 != X1_57
% 2.31/0.99      | X0_56 != X3_56
% 2.31/0.99      | X1_56 != X4_56
% 2.31/0.99      | X2_56 != X5_56 ),
% 2.31/0.99      theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2293,plain,
% 2.31/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3)
% 2.31/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 2.31/0.99      | sK2 != sK2
% 2.31/0.99      | sK3 != sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1728]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2341,plain,
% 2.31/0.99      ( sK3 = sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1706]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1711,plain,
% 2.31/0.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 2.31/0.99      theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2400,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) != X0_57
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != X0_57
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1711]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3469,plain,
% 2.31/0.99      ( k9_tmap_1(sK2,sK3) != k6_partfun1(u1_struct_0(sK2))
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK2)) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_2400]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3548,plain,
% 2.31/0.99      ( v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_3102,c_26,c_743,c_1749,c_1701,c_1695,c_2264,c_2293,
% 2.31/0.99                 c_2341,c_2831,c_2832,c_2833,c_3469]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3549,plain,
% 2.31/0.99      ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_3548]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2683,plain,
% 2.31/0.99      ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3)
% 2.31/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 2.31/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2538,c_2169]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2267,plain,
% 2.31/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1691]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2268,plain,
% 2.31/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.31/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3424,plain,
% 2.31/0.99      ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2683,c_31,c_744,c_1749,c_1701,c_1695,c_2268,c_2293,
% 2.31/0.99                 c_2341,c_2358]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3426,plain,
% 2.31/0.99      ( sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK3) ),
% 2.31/0.99      inference(light_normalisation,[status(thm)],[c_3424,c_2398]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3554,plain,
% 2.31/0.99      ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top
% 2.31/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.31/0.99      inference(light_normalisation,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_3549,c_1698,c_1701,c_3426]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3559,plain,
% 2.31/0.99      ( v1_funct_2(X0_57,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.31/0.99      | v1_funct_1(X0_57) != iProver_top ),
% 2.31/0.99      inference(forward_subsumption_resolution,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_3554,c_2103]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3563,plain,
% 2.31/0.99      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.31/0.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2832,c_3559]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(contradiction,plain,
% 2.31/0.99      ( $false ),
% 2.31/0.99      inference(minisat,[status(thm)],[c_3563,c_2833,c_2831]) ).
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  ------                               Statistics
% 2.31/0.99  
% 2.31/0.99  ------ General
% 2.31/0.99  
% 2.31/0.99  abstr_ref_over_cycles:                  0
% 2.31/0.99  abstr_ref_under_cycles:                 0
% 2.31/0.99  gc_basic_clause_elim:                   0
% 2.31/0.99  forced_gc_time:                         0
% 2.31/0.99  parsing_time:                           0.011
% 2.31/0.99  unif_index_cands_time:                  0.
% 2.31/0.99  unif_index_add_time:                    0.
% 2.31/0.99  orderings_time:                         0.
% 2.31/0.99  out_proof_time:                         0.021
% 2.31/0.99  total_time:                             0.166
% 2.31/0.99  num_of_symbols:                         66
% 2.31/0.99  num_of_terms:                           3670
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing
% 2.31/0.99  
% 2.31/0.99  num_of_splits:                          0
% 2.31/0.99  num_of_split_atoms:                     0
% 2.31/0.99  num_of_reused_defs:                     0
% 2.31/0.99  num_eq_ax_congr_red:                    12
% 2.31/0.99  num_of_sem_filtered_clauses:            6
% 2.31/0.99  num_of_subtypes:                        4
% 2.31/0.99  monotx_restored_types:                  0
% 2.31/0.99  sat_num_of_epr_types:                   0
% 2.31/0.99  sat_num_of_non_cyclic_types:            0
% 2.31/0.99  sat_guarded_non_collapsed_types:        1
% 2.31/0.99  num_pure_diseq_elim:                    0
% 2.31/0.99  simp_replaced_by:                       0
% 2.31/0.99  res_preprocessed:                       138
% 2.31/0.99  prep_upred:                             0
% 2.31/0.99  prep_unflattend:                        59
% 2.31/0.99  smt_new_axioms:                         0
% 2.31/0.99  pred_elim_cands:                        5
% 2.31/0.99  pred_elim:                              7
% 2.31/0.99  pred_elim_cl:                           8
% 2.31/0.99  pred_elim_cycles:                       11
% 2.31/0.99  merged_defs:                            0
% 2.31/0.99  merged_defs_ncl:                        0
% 2.31/0.99  bin_hyper_res:                          0
% 2.31/0.99  prep_cycles:                            4
% 2.31/0.99  pred_elim_time:                         0.031
% 2.31/0.99  splitting_time:                         0.
% 2.31/0.99  sem_filter_time:                        0.
% 2.31/0.99  monotx_time:                            0.
% 2.31/0.99  subtype_inf_time:                       0.
% 2.31/0.99  
% 2.31/0.99  ------ Problem properties
% 2.31/0.99  
% 2.31/0.99  clauses:                                21
% 2.31/0.99  conjectures:                            3
% 2.31/0.99  epr:                                    2
% 2.31/0.99  horn:                                   14
% 2.31/0.99  ground:                                 10
% 2.31/0.99  unary:                                  9
% 2.31/0.99  binary:                                 5
% 2.31/0.99  lits:                                   51
% 2.31/0.99  lits_eq:                                11
% 2.31/0.99  fd_pure:                                0
% 2.31/0.99  fd_pseudo:                              0
% 2.31/0.99  fd_cond:                                3
% 2.31/0.99  fd_pseudo_cond:                         0
% 2.31/0.99  ac_symbols:                             0
% 2.31/0.99  
% 2.31/0.99  ------ Propositional Solver
% 2.31/0.99  
% 2.31/0.99  prop_solver_calls:                      27
% 2.31/0.99  prop_fast_solver_calls:                 1334
% 2.31/0.99  smt_solver_calls:                       0
% 2.31/0.99  smt_fast_solver_calls:                  0
% 2.31/0.99  prop_num_of_clauses:                    1000
% 2.31/0.99  prop_preprocess_simplified:             4051
% 2.31/0.99  prop_fo_subsumed:                       85
% 2.31/0.99  prop_solver_time:                       0.
% 2.31/0.99  smt_solver_time:                        0.
% 2.31/0.99  smt_fast_solver_time:                   0.
% 2.31/0.99  prop_fast_solver_time:                  0.
% 2.31/0.99  prop_unsat_core_time:                   0.
% 2.31/0.99  
% 2.31/0.99  ------ QBF
% 2.31/0.99  
% 2.31/0.99  qbf_q_res:                              0
% 2.31/0.99  qbf_num_tautologies:                    0
% 2.31/0.99  qbf_prep_cycles:                        0
% 2.31/0.99  
% 2.31/0.99  ------ BMC1
% 2.31/0.99  
% 2.31/0.99  bmc1_current_bound:                     -1
% 2.31/0.99  bmc1_last_solved_bound:                 -1
% 2.31/0.99  bmc1_unsat_core_size:                   -1
% 2.31/0.99  bmc1_unsat_core_parents_size:           -1
% 2.31/0.99  bmc1_merge_next_fun:                    0
% 2.31/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.31/0.99  
% 2.31/0.99  ------ Instantiation
% 2.31/0.99  
% 2.31/0.99  inst_num_of_clauses:                    271
% 2.31/0.99  inst_num_in_passive:                    70
% 2.31/0.99  inst_num_in_active:                     180
% 2.31/0.99  inst_num_in_unprocessed:                21
% 2.31/0.99  inst_num_of_loops:                      190
% 2.31/0.99  inst_num_of_learning_restarts:          0
% 2.31/0.99  inst_num_moves_active_passive:          5
% 2.31/0.99  inst_lit_activity:                      0
% 2.31/0.99  inst_lit_activity_moves:                0
% 2.31/0.99  inst_num_tautologies:                   0
% 2.31/0.99  inst_num_prop_implied:                  0
% 2.31/0.99  inst_num_existing_simplified:           0
% 2.31/0.99  inst_num_eq_res_simplified:             0
% 2.31/0.99  inst_num_child_elim:                    0
% 2.31/0.99  inst_num_of_dismatching_blockings:      53
% 2.31/0.99  inst_num_of_non_proper_insts:           240
% 2.31/0.99  inst_num_of_duplicates:                 0
% 2.31/0.99  inst_inst_num_from_inst_to_res:         0
% 2.31/0.99  inst_dismatching_checking_time:         0.
% 2.31/0.99  
% 2.31/0.99  ------ Resolution
% 2.31/0.99  
% 2.31/0.99  res_num_of_clauses:                     0
% 2.31/0.99  res_num_in_passive:                     0
% 2.31/0.99  res_num_in_active:                      0
% 2.31/0.99  res_num_of_loops:                       142
% 2.31/0.99  res_forward_subset_subsumed:            64
% 2.31/0.99  res_backward_subset_subsumed:           0
% 2.31/0.99  res_forward_subsumed:                   0
% 2.31/0.99  res_backward_subsumed:                  0
% 2.31/0.99  res_forward_subsumption_resolution:     7
% 2.31/0.99  res_backward_subsumption_resolution:    1
% 2.31/0.99  res_clause_to_clause_subsumption:       118
% 2.31/0.99  res_orphan_elimination:                 0
% 2.31/0.99  res_tautology_del:                      64
% 2.31/0.99  res_num_eq_res_simplified:              0
% 2.31/0.99  res_num_sel_changes:                    0
% 2.31/0.99  res_moves_from_active_to_pass:          0
% 2.31/0.99  
% 2.31/0.99  ------ Superposition
% 2.31/0.99  
% 2.31/0.99  sup_time_total:                         0.
% 2.31/0.99  sup_time_generating:                    0.
% 2.31/0.99  sup_time_sim_full:                      0.
% 2.31/0.99  sup_time_sim_immed:                     0.
% 2.31/0.99  
% 2.31/0.99  sup_num_of_clauses:                     28
% 2.31/0.99  sup_num_in_active:                      27
% 2.31/0.99  sup_num_in_passive:                     1
% 2.31/0.99  sup_num_of_loops:                       36
% 2.31/0.99  sup_fw_superposition:                   12
% 2.31/0.99  sup_bw_superposition:                   13
% 2.31/0.99  sup_immediate_simplified:               13
% 2.31/0.99  sup_given_eliminated:                   0
% 2.31/0.99  comparisons_done:                       0
% 2.31/0.99  comparisons_avoided:                    3
% 2.31/0.99  
% 2.31/0.99  ------ Simplifications
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  sim_fw_subset_subsumed:                 6
% 2.31/0.99  sim_bw_subset_subsumed:                 1
% 2.31/0.99  sim_fw_subsumed:                        3
% 2.31/0.99  sim_bw_subsumed:                        0
% 2.31/0.99  sim_fw_subsumption_res:                 2
% 2.31/0.99  sim_bw_subsumption_res:                 0
% 2.31/0.99  sim_tautology_del:                      0
% 2.31/0.99  sim_eq_tautology_del:                   0
% 2.31/0.99  sim_eq_res_simp:                        1
% 2.31/0.99  sim_fw_demodulated:                     0
% 2.31/0.99  sim_bw_demodulated:                     9
% 2.31/0.99  sim_light_normalised:                   20
% 2.31/0.99  sim_joinable_taut:                      0
% 2.31/0.99  sim_joinable_simp:                      0
% 2.31/0.99  sim_ac_normalised:                      0
% 2.31/0.99  sim_smt_subsumption:                    0
% 2.31/0.99  
%------------------------------------------------------------------------------
