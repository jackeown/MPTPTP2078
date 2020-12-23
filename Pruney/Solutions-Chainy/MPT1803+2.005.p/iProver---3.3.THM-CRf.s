%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:09 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  301 (31483 expanded)
%              Number of clauses        :  221 (8027 expanded)
%              Number of leaves         :   18 (9161 expanded)
%              Depth                    :   37
%              Number of atoms          : 1565 (182626 expanded)
%              Number of equality atoms :  523 (13536 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4)
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f49,plain,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f48,f47,f46])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f10,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f79,plain,(
    ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_195,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_21,c_17,c_16,c_15])).

cnf(c_196,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_965,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_25])).

cnf(c_966,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_968,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_29,c_28,c_27])).

cnf(c_3680,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_968])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_2624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2623])).

cnf(c_2628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2624,c_28,c_27])).

cnf(c_3649,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) ),
    inference(subtyping,[status(esa)],[c_2628])).

cnf(c_4813,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_6169,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_4813])).

cnf(c_973,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_974,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_976,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_27])).

cnf(c_3679,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_4777,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3679])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_2570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2569])).

cnf(c_2574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2570,c_28,c_27])).

cnf(c_3652,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0_56)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2574])).

cnf(c_4810,plain,
    ( u1_struct_0(k6_tmap_1(sK2,X0_56)) = u1_struct_0(sK2)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_5377,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4777,c_4810])).

cnf(c_5380,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5377,c_3680])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_29])).

cnf(c_2642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2641])).

cnf(c_2646,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2642,c_28,c_27])).

cnf(c_3648,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_2646])).

cnf(c_4814,plain,
    ( k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3648])).

cnf(c_5560,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_4777,c_4814])).

cnf(c_6170,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6169,c_5380,c_5560])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_975,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_6930,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6170,c_32,c_975])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_22,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1130,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_1131,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1130])).

cnf(c_2465,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1131,c_29])).

cnf(c_2466,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2465])).

cnf(c_2470,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2466,c_28,c_27])).

cnf(c_2471,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_3654,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0_56)
    | sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0_56 ),
    inference(subtyping,[status(esa)],[c_2471])).

cnf(c_4808,plain,
    ( sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_809,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_22])).

cnf(c_810,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_3681,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_810])).

cnf(c_4776,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3681])).

cnf(c_5378,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_4810])).

cnf(c_791,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | X1 != X0
    | X1 != X2
    | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_196,c_22])).

cnf(c_792,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_2183,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_792,c_29])).

cnf(c_2184,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_2183])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_41,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_53,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_56,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_59,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_83,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2186,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2184,c_29,c_28,c_27,c_38,c_41,c_53,c_56,c_59,c_83])).

cnf(c_3664,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(subtyping,[status(esa)],[c_2186])).

cnf(c_5379,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5378,c_3664])).

cnf(c_5445,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5379,c_32])).

cnf(c_6722,plain,
    ( sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4808,c_5445])).

cnf(c_6935,plain,
    ( sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6930,c_6722])).

cnf(c_5561,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2))
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_4814])).

cnf(c_5002,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3648])).

cnf(c_5737,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5561,c_27,c_38,c_41,c_5002])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_2606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2605])).

cnf(c_2610,plain,
    ( v1_funct_1(k7_tmap_1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_28,c_27])).

cnf(c_2611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_2610])).

cnf(c_3650,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_56)) ),
    inference(subtyping,[status(esa)],[c_2611])).

cnf(c_4812,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,X0_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_5373,plain,
    ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_4812])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_5013,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3650])).

cnf(c_5014,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5013])).

cnf(c_5732,plain,
    ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5373,c_32,c_39,c_42,c_5014])).

cnf(c_5739,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5737,c_5732])).

cnf(c_13,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2249,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_2250,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2249])).

cnf(c_2254,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2250,c_28,c_27])).

cnf(c_3662,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_2254])).

cnf(c_4793,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3662])).

cnf(c_5930,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_4793])).

cnf(c_5931,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5930,c_5380,c_5560])).

cnf(c_9679,plain,
    ( sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK2)
    | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6935,c_32,c_975,c_5739,c_5931])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1100,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_1101,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1100])).

cnf(c_2492,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1101,c_29])).

cnf(c_2493,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2492])).

cnf(c_2497,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2493,c_28,c_27])).

cnf(c_2498,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2497])).

cnf(c_3653,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_56)
    | k9_tmap_1(sK2,sK2) = X0_56 ),
    inference(subtyping,[status(esa)],[c_2498])).

cnf(c_4809,plain,
    ( k9_tmap_1(sK2,sK2) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3653])).

cnf(c_6825,plain,
    ( k9_tmap_1(sK2,sK2) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4809,c_5445])).

cnf(c_6934,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6930,c_6825])).

cnf(c_8857,plain,
    ( m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6934,c_32,c_975,c_5739,c_5931])).

cnf(c_8858,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8857])).

cnf(c_8862,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_8858,c_4814])).

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
    inference(cnf_transformation,[],[f52])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_711,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X0
    | k9_tmap_1(X0,X1) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_712,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_2191,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_712,c_29])).

cnf(c_2192,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_2191])).

cnf(c_2196,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2192,c_28,c_27])).

cnf(c_2197,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2196])).

cnf(c_2907,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | X6 != X3
    | k9_tmap_1(sK2,sK2) = X6
    | k7_tmap_1(sK2,sK1(sK2,sK2,X6)) != X3
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X6))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK2)) != X5
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_2197])).

cnf(c_2908,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k9_tmap_1(sK2,sK2) = X1
    | k7_tmap_1(sK2,sK1(sK2,sK2,X1)) != X1 ),
    inference(unflattening,[status(thm)],[c_2907])).

cnf(c_3646,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))
    | ~ v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X1_56)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
    | k9_tmap_1(sK2,sK2) = X1_56
    | k7_tmap_1(sK2,sK1(sK2,sK2,X1_56)) != X1_56 ),
    inference(subtyping,[status(esa)],[c_2908])).

cnf(c_4817,plain,
    ( k9_tmap_1(sK2,sK2) = X0_56
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
    | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3646])).

cnf(c_5447,plain,
    ( k9_tmap_1(sK2,sK2) = X0_56
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
    | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5445,c_4817])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_100,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_102,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_103,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_105,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_6982,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
    | k9_tmap_1(sK2,sK2) = X0_56 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5447,c_30,c_32,c_102,c_105])).

cnf(c_6983,plain,
    ( k9_tmap_1(sK2,sK2) = X0_56
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
    | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6982])).

cnf(c_8868,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8862,c_6983])).

cnf(c_10991,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8868,c_32,c_975,c_5739,c_5931,c_6170])).

cnf(c_10992,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10991])).

cnf(c_11000,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9679,c_10992])).

cnf(c_11001,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11000,c_3664,c_5445])).

cnf(c_8867,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8862,c_4793])).

cnf(c_9917,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
    | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8867,c_8858])).

cnf(c_9918,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9917])).

cnf(c_8866,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8862,c_4813])).

cnf(c_10174,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8866,c_8858])).

cnf(c_10998,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10174,c_10992])).

cnf(c_11051,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11001,c_5739,c_9918,c_10998])).

cnf(c_11056,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9679,c_11051])).

cnf(c_11057,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11056,c_3664,c_5445])).

cnf(c_11060,plain,
    ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11057,c_30,c_32,c_102,c_105])).

cnf(c_11,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_741,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_742,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_744,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_29,c_28,c_27])).

cnf(c_745,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_744])).

cnf(c_983,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_976,c_745])).

cnf(c_3058,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k9_tmap_1(sK2,sK2) = X0
    | k9_tmap_1(sK2,sK3) != X0
    | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_983,c_2197])).

cnf(c_3059,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_3058])).

cnf(c_3642,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_3059])).

cnf(c_4821,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3642])).

cnf(c_4840,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4821,c_3680])).

cnf(c_6523,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4840,c_5380,c_5445,c_5560])).

cnf(c_6524,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6523])).

cnf(c_11069,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11060,c_6524])).

cnf(c_1160,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_1161,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1160])).

cnf(c_1165,plain,
    ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_29,c_28,c_27])).

cnf(c_1166,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1165])).

cnf(c_3676,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_56)
    | k9_tmap_1(sK2,sK3) = X0_56 ),
    inference(subtyping,[status(esa)],[c_1166])).

cnf(c_4780,plain,
    ( k9_tmap_1(sK2,sK3) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3676])).

cnf(c_6176,plain,
    ( k9_tmap_1(sK2,sK3) = X0_56
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4780,c_5380])).

cnf(c_6937,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6930,c_6176])).

cnf(c_10218,plain,
    ( m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6937,c_32,c_975,c_5739,c_5931])).

cnf(c_10219,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10218])).

cnf(c_10224,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_10219,c_4814])).

cnf(c_10225,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_10219,c_4810])).

cnf(c_681,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_682,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
    | ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_2218,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
    | ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_682,c_29])).

cnf(c_2219,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2218])).

cnf(c_684,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_2221,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_29,c_28,c_27,c_38,c_41,c_684])).

cnf(c_2222,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2)) ),
    inference(renaming,[status(thm)],[c_2221])).

cnf(c_764,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_765,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_765,c_29,c_28,c_27])).

cnf(c_770,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_769])).

cnf(c_2943,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | k9_tmap_1(sK2,sK2) != X0
    | k9_tmap_1(sK2,sK3) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_2222,c_770])).

cnf(c_2944,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_2943])).

cnf(c_3645,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
    | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_2944])).

cnf(c_4818,plain,
    ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3645])).

cnf(c_4839,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4818,c_3664])).

cnf(c_6436,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4839,c_5380,c_5445,c_5737])).

cnf(c_6437,plain,
    ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6436])).

cnf(c_11070,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))))) != u1_struct_0(sK2)
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11060,c_6437])).

cnf(c_11283,plain,
    ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11069,c_32,c_975,c_5739,c_5931,c_6170,c_10224,c_10225,c_11070])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_177,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_372,plain,
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
    inference(resolution_lifted,[status(thm)],[c_177,c_23])).

cnf(c_373,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_377,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_26,c_24])).

cnf(c_378,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1234,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_378])).

cnf(c_1235,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_380,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_1237,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_29,c_28,c_27,c_25,c_380,c_966])).

cnf(c_3673,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(subtyping,[status(esa)],[c_1237])).

cnf(c_4838,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(light_normalisation,[status(thm)],[c_3673,c_3680])).

cnf(c_6111,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(light_normalisation,[status(thm)],[c_4838,c_5560])).

cnf(c_11291,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) ),
    inference(demodulation,[status(thm)],[c_11283,c_6111])).

cnf(c_11292,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11291])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.00  
% 3.37/1.00  ------  iProver source info
% 3.37/1.00  
% 3.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.00  git: non_committed_changes: false
% 3.37/1.00  git: last_make_outside_of_git: false
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    ""
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         true
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     num_symb
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       true
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     true
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_input_bw                          []
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  ------ Parsing...
% 3.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... gs_s  sp: 9 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  ------ Proving...
% 3.37/1.00  ------ Problem Properties 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  clauses                                 72
% 3.37/1.00  conjectures                             3
% 3.37/1.00  EPR                                     10
% 3.37/1.00  Horn                                    50
% 3.37/1.00  unary                                   12
% 3.37/1.00  binary                                  14
% 3.37/1.00  lits                                    275
% 3.37/1.00  lits eq                                 85
% 3.37/1.00  fd_pure                                 0
% 3.37/1.00  fd_pseudo                               0
% 3.37/1.00  fd_cond                                 9
% 3.37/1.00  fd_pseudo_cond                          0
% 3.37/1.00  AC symbols                              0
% 3.37/1.00  
% 3.37/1.00  ------ Schedule dynamic 5 is on 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  Current options:
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  ------ Input Options
% 3.37/1.00  
% 3.37/1.00  --out_options                           all
% 3.37/1.00  --tptp_safe_out                         true
% 3.37/1.00  --problem_path                          ""
% 3.37/1.00  --include_path                          ""
% 3.37/1.00  --clausifier                            res/vclausify_rel
% 3.37/1.00  --clausifier_options                    ""
% 3.37/1.00  --stdin                                 false
% 3.37/1.00  --stats_out                             all
% 3.37/1.00  
% 3.37/1.00  ------ General Options
% 3.37/1.00  
% 3.37/1.00  --fof                                   false
% 3.37/1.00  --time_out_real                         305.
% 3.37/1.00  --time_out_virtual                      -1.
% 3.37/1.00  --symbol_type_check                     false
% 3.37/1.00  --clausify_out                          false
% 3.37/1.00  --sig_cnt_out                           false
% 3.37/1.00  --trig_cnt_out                          false
% 3.37/1.00  --trig_cnt_out_tolerance                1.
% 3.37/1.00  --trig_cnt_out_sk_spl                   false
% 3.37/1.00  --abstr_cl_out                          false
% 3.37/1.00  
% 3.37/1.00  ------ Global Options
% 3.37/1.00  
% 3.37/1.00  --schedule                              default
% 3.37/1.00  --add_important_lit                     false
% 3.37/1.00  --prop_solver_per_cl                    1000
% 3.37/1.00  --min_unsat_core                        false
% 3.37/1.00  --soft_assumptions                      false
% 3.37/1.00  --soft_lemma_size                       3
% 3.37/1.00  --prop_impl_unit_size                   0
% 3.37/1.00  --prop_impl_unit                        []
% 3.37/1.00  --share_sel_clauses                     true
% 3.37/1.00  --reset_solvers                         false
% 3.37/1.00  --bc_imp_inh                            [conj_cone]
% 3.37/1.00  --conj_cone_tolerance                   3.
% 3.37/1.00  --extra_neg_conj                        none
% 3.37/1.00  --large_theory_mode                     true
% 3.37/1.00  --prolific_symb_bound                   200
% 3.37/1.00  --lt_threshold                          2000
% 3.37/1.00  --clause_weak_htbl                      true
% 3.37/1.00  --gc_record_bc_elim                     false
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing Options
% 3.37/1.00  
% 3.37/1.00  --preprocessing_flag                    true
% 3.37/1.00  --time_out_prep_mult                    0.1
% 3.37/1.00  --splitting_mode                        input
% 3.37/1.00  --splitting_grd                         true
% 3.37/1.00  --splitting_cvd                         false
% 3.37/1.00  --splitting_cvd_svl                     false
% 3.37/1.00  --splitting_nvd                         32
% 3.37/1.00  --sub_typing                            true
% 3.37/1.00  --prep_gs_sim                           true
% 3.37/1.00  --prep_unflatten                        true
% 3.37/1.00  --prep_res_sim                          true
% 3.37/1.00  --prep_upred                            true
% 3.37/1.00  --prep_sem_filter                       exhaustive
% 3.37/1.00  --prep_sem_filter_out                   false
% 3.37/1.00  --pred_elim                             true
% 3.37/1.00  --res_sim_input                         true
% 3.37/1.00  --eq_ax_congr_red                       true
% 3.37/1.00  --pure_diseq_elim                       true
% 3.37/1.00  --brand_transform                       false
% 3.37/1.00  --non_eq_to_eq                          false
% 3.37/1.00  --prep_def_merge                        true
% 3.37/1.00  --prep_def_merge_prop_impl              false
% 3.37/1.00  --prep_def_merge_mbd                    true
% 3.37/1.00  --prep_def_merge_tr_red                 false
% 3.37/1.00  --prep_def_merge_tr_cl                  false
% 3.37/1.00  --smt_preprocessing                     true
% 3.37/1.00  --smt_ac_axioms                         fast
% 3.37/1.00  --preprocessed_out                      false
% 3.37/1.00  --preprocessed_stats                    false
% 3.37/1.00  
% 3.37/1.00  ------ Abstraction refinement Options
% 3.37/1.00  
% 3.37/1.00  --abstr_ref                             []
% 3.37/1.00  --abstr_ref_prep                        false
% 3.37/1.00  --abstr_ref_until_sat                   false
% 3.37/1.00  --abstr_ref_sig_restrict                funpre
% 3.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.00  --abstr_ref_under                       []
% 3.37/1.00  
% 3.37/1.00  ------ SAT Options
% 3.37/1.00  
% 3.37/1.00  --sat_mode                              false
% 3.37/1.00  --sat_fm_restart_options                ""
% 3.37/1.00  --sat_gr_def                            false
% 3.37/1.00  --sat_epr_types                         true
% 3.37/1.00  --sat_non_cyclic_types                  false
% 3.37/1.00  --sat_finite_models                     false
% 3.37/1.00  --sat_fm_lemmas                         false
% 3.37/1.00  --sat_fm_prep                           false
% 3.37/1.00  --sat_fm_uc_incr                        true
% 3.37/1.00  --sat_out_model                         small
% 3.37/1.00  --sat_out_clauses                       false
% 3.37/1.00  
% 3.37/1.00  ------ QBF Options
% 3.37/1.00  
% 3.37/1.00  --qbf_mode                              false
% 3.37/1.00  --qbf_elim_univ                         false
% 3.37/1.00  --qbf_dom_inst                          none
% 3.37/1.00  --qbf_dom_pre_inst                      false
% 3.37/1.00  --qbf_sk_in                             false
% 3.37/1.00  --qbf_pred_elim                         true
% 3.37/1.00  --qbf_split                             512
% 3.37/1.00  
% 3.37/1.00  ------ BMC1 Options
% 3.37/1.00  
% 3.37/1.00  --bmc1_incremental                      false
% 3.37/1.00  --bmc1_axioms                           reachable_all
% 3.37/1.00  --bmc1_min_bound                        0
% 3.37/1.00  --bmc1_max_bound                        -1
% 3.37/1.00  --bmc1_max_bound_default                -1
% 3.37/1.00  --bmc1_symbol_reachability              true
% 3.37/1.00  --bmc1_property_lemmas                  false
% 3.37/1.00  --bmc1_k_induction                      false
% 3.37/1.00  --bmc1_non_equiv_states                 false
% 3.37/1.00  --bmc1_deadlock                         false
% 3.37/1.00  --bmc1_ucm                              false
% 3.37/1.00  --bmc1_add_unsat_core                   none
% 3.37/1.00  --bmc1_unsat_core_children              false
% 3.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.00  --bmc1_out_stat                         full
% 3.37/1.00  --bmc1_ground_init                      false
% 3.37/1.00  --bmc1_pre_inst_next_state              false
% 3.37/1.00  --bmc1_pre_inst_state                   false
% 3.37/1.00  --bmc1_pre_inst_reach_state             false
% 3.37/1.00  --bmc1_out_unsat_core                   false
% 3.37/1.00  --bmc1_aig_witness_out                  false
% 3.37/1.00  --bmc1_verbose                          false
% 3.37/1.00  --bmc1_dump_clauses_tptp                false
% 3.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.00  --bmc1_dump_file                        -
% 3.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.00  --bmc1_ucm_extend_mode                  1
% 3.37/1.00  --bmc1_ucm_init_mode                    2
% 3.37/1.00  --bmc1_ucm_cone_mode                    none
% 3.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.00  --bmc1_ucm_relax_model                  4
% 3.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.00  --bmc1_ucm_layered_model                none
% 3.37/1.00  --bmc1_ucm_max_lemma_size               10
% 3.37/1.00  
% 3.37/1.00  ------ AIG Options
% 3.37/1.00  
% 3.37/1.00  --aig_mode                              false
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation Options
% 3.37/1.00  
% 3.37/1.00  --instantiation_flag                    true
% 3.37/1.00  --inst_sos_flag                         true
% 3.37/1.00  --inst_sos_phase                        true
% 3.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.00  --inst_lit_sel_side                     none
% 3.37/1.00  --inst_solver_per_active                1400
% 3.37/1.00  --inst_solver_calls_frac                1.
% 3.37/1.00  --inst_passive_queue_type               priority_queues
% 3.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.00  --inst_passive_queues_freq              [25;2]
% 3.37/1.00  --inst_dismatching                      true
% 3.37/1.00  --inst_eager_unprocessed_to_passive     true
% 3.37/1.00  --inst_prop_sim_given                   true
% 3.37/1.00  --inst_prop_sim_new                     false
% 3.37/1.00  --inst_subs_new                         false
% 3.37/1.00  --inst_eq_res_simp                      false
% 3.37/1.00  --inst_subs_given                       false
% 3.37/1.00  --inst_orphan_elimination               true
% 3.37/1.00  --inst_learning_loop_flag               true
% 3.37/1.00  --inst_learning_start                   3000
% 3.37/1.00  --inst_learning_factor                  2
% 3.37/1.00  --inst_start_prop_sim_after_learn       3
% 3.37/1.00  --inst_sel_renew                        solver
% 3.37/1.00  --inst_lit_activity_flag                true
% 3.37/1.00  --inst_restr_to_given                   false
% 3.37/1.00  --inst_activity_threshold               500
% 3.37/1.00  --inst_out_proof                        true
% 3.37/1.00  
% 3.37/1.00  ------ Resolution Options
% 3.37/1.00  
% 3.37/1.00  --resolution_flag                       false
% 3.37/1.00  --res_lit_sel                           adaptive
% 3.37/1.00  --res_lit_sel_side                      none
% 3.37/1.00  --res_ordering                          kbo
% 3.37/1.00  --res_to_prop_solver                    active
% 3.37/1.00  --res_prop_simpl_new                    false
% 3.37/1.00  --res_prop_simpl_given                  true
% 3.37/1.00  --res_passive_queue_type                priority_queues
% 3.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.00  --res_passive_queues_freq               [15;5]
% 3.37/1.00  --res_forward_subs                      full
% 3.37/1.00  --res_backward_subs                     full
% 3.37/1.00  --res_forward_subs_resolution           true
% 3.37/1.00  --res_backward_subs_resolution          true
% 3.37/1.00  --res_orphan_elimination                true
% 3.37/1.00  --res_time_limit                        2.
% 3.37/1.00  --res_out_proof                         true
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Options
% 3.37/1.00  
% 3.37/1.00  --superposition_flag                    true
% 3.37/1.00  --sup_passive_queue_type                priority_queues
% 3.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.00  --demod_completeness_check              fast
% 3.37/1.00  --demod_use_ground                      true
% 3.37/1.00  --sup_to_prop_solver                    passive
% 3.37/1.00  --sup_prop_simpl_new                    true
% 3.37/1.00  --sup_prop_simpl_given                  true
% 3.37/1.00  --sup_fun_splitting                     true
% 3.37/1.00  --sup_smt_interval                      50000
% 3.37/1.00  
% 3.37/1.00  ------ Superposition Simplification Setup
% 3.37/1.00  
% 3.37/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.00  --sup_immed_triv                        [TrivRules]
% 3.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_immed_bw_main                     []
% 3.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.00  --sup_input_bw                          []
% 3.37/1.00  
% 3.37/1.00  ------ Combination Options
% 3.37/1.00  
% 3.37/1.00  --comb_res_mult                         3
% 3.37/1.00  --comb_sup_mult                         2
% 3.37/1.00  --comb_inst_mult                        10
% 3.37/1.00  
% 3.37/1.00  ------ Debug Options
% 3.37/1.00  
% 3.37/1.00  --dbg_backtrace                         false
% 3.37/1.00  --dbg_dump_prop_clauses                 false
% 3.37/1.00  --dbg_dump_prop_clauses_file            -
% 3.37/1.00  --dbg_out_stat                          false
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS status Theorem for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00   Resolution empty clause
% 3.37/1.00  
% 3.37/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  fof(f5,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f22,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f23,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f22])).
% 3.37/1.00  
% 3.37/1.00  fof(f38,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f23])).
% 3.37/1.00  
% 3.37/1.00  fof(f39,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(rectify,[],[f38])).
% 3.37/1.00  
% 3.37/1.00  fof(f40,plain,(
% 3.37/1.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f41,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.37/1.00  
% 3.37/1.00  fof(f54,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f41])).
% 3.37/1.00  
% 3.37/1.00  fof(f80,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f54])).
% 3.37/1.00  
% 3.37/1.00  fof(f81,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f80])).
% 3.37/1.00  
% 3.37/1.00  fof(f11,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f34,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f11])).
% 3.37/1.00  
% 3.37/1.00  fof(f71,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f34])).
% 3.37/1.00  
% 3.37/1.00  fof(f8,axiom,(
% 3.37/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f28,plain,(
% 3.37/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f8])).
% 3.37/1.00  
% 3.37/1.00  fof(f29,plain,(
% 3.37/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f28])).
% 3.37/1.00  
% 3.37/1.00  fof(f65,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f66,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f67,plain,(
% 3.37/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f29])).
% 3.37/1.00  
% 3.37/1.00  fof(f13,conjecture,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f14,negated_conjecture,(
% 3.37/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.37/1.00    inference(negated_conjecture,[],[f13])).
% 3.37/1.00  
% 3.37/1.00  fof(f36,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f37,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f36])).
% 3.37/1.00  
% 3.37/1.00  fof(f48,plain,(
% 3.37/1.00    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f47,plain,(
% 3.37/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f46,plain,(
% 3.37/1.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f49,plain,(
% 3.37/1.00    ((~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f48,f47,f46])).
% 3.37/1.00  
% 3.37/1.00  fof(f77,plain,(
% 3.37/1.00    m1_pre_topc(sK3,sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f73,plain,(
% 3.37/1.00    ~v2_struct_0(sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f74,plain,(
% 3.37/1.00    v2_pre_topc(sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f75,plain,(
% 3.37/1.00    l1_pre_topc(sK2)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f7,axiom,(
% 3.37/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f26,plain,(
% 3.37/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f7])).
% 3.37/1.00  
% 3.37/1.00  fof(f27,plain,(
% 3.37/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f26])).
% 3.37/1.00  
% 3.37/1.00  fof(f64,plain,(
% 3.37/1.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f9,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f30,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f9])).
% 3.37/1.00  
% 3.37/1.00  fof(f31,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f30])).
% 3.37/1.00  
% 3.37/1.00  fof(f68,plain,(
% 3.37/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f31])).
% 3.37/1.00  
% 3.37/1.00  fof(f4,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f20,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f4])).
% 3.37/1.00  
% 3.37/1.00  fof(f21,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f20])).
% 3.37/1.00  
% 3.37/1.00  fof(f53,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f6,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f24,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f6])).
% 3.37/1.00  
% 3.37/1.00  fof(f25,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f24])).
% 3.37/1.00  
% 3.37/1.00  fof(f42,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(nnf_transformation,[],[f25])).
% 3.37/1.00  
% 3.37/1.00  fof(f43,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(rectify,[],[f42])).
% 3.37/1.00  
% 3.37/1.00  fof(f44,plain,(
% 3.37/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f45,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 3.37/1.00  
% 3.37/1.00  fof(f60,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f12,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f35,plain,(
% 3.37/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f12])).
% 3.37/1.00  
% 3.37/1.00  fof(f72,plain,(
% 3.37/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f35])).
% 3.37/1.00  
% 3.37/1.00  fof(f62,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f63,plain,(
% 3.37/1.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  fof(f59,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f3,axiom,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f18,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.37/1.00    inference(ennf_transformation,[],[f3])).
% 3.37/1.00  
% 3.37/1.00  fof(f19,plain,(
% 3.37/1.00    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.37/1.00    inference(flattening,[],[f18])).
% 3.37/1.00  
% 3.37/1.00  fof(f52,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f19])).
% 3.37/1.00  
% 3.37/1.00  fof(f61,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f2,axiom,(
% 3.37/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f16,plain,(
% 3.37/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f2])).
% 3.37/1.00  
% 3.37/1.00  fof(f17,plain,(
% 3.37/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f16])).
% 3.37/1.00  
% 3.37/1.00  fof(f51,plain,(
% 3.37/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f17])).
% 3.37/1.00  
% 3.37/1.00  fof(f1,axiom,(
% 3.37/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f15,plain,(
% 3.37/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.37/1.00    inference(ennf_transformation,[],[f1])).
% 3.37/1.00  
% 3.37/1.00  fof(f50,plain,(
% 3.37/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f15])).
% 3.37/1.00  
% 3.37/1.00  fof(f58,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f82,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f58])).
% 3.37/1.00  
% 3.37/1.00  fof(f83,plain,(
% 3.37/1.00    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f82])).
% 3.37/1.00  
% 3.37/1.00  fof(f10,axiom,(
% 3.37/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 3.37/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f32,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/1.00    inference(ennf_transformation,[],[f10])).
% 3.37/1.00  
% 3.37/1.00  fof(f33,plain,(
% 3.37/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/1.00    inference(flattening,[],[f32])).
% 3.37/1.00  
% 3.37/1.00  fof(f70,plain,(
% 3.37/1.00    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f33])).
% 3.37/1.00  
% 3.37/1.00  fof(f84,plain,(
% 3.37/1.00    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/1.00    inference(equality_resolution,[],[f70])).
% 3.37/1.00  
% 3.37/1.00  fof(f79,plain,(
% 3.37/1.00    ~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f76,plain,(
% 3.37/1.00    ~v2_struct_0(sK3)),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  fof(f78,plain,(
% 3.37/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.37/1.00    inference(cnf_transformation,[],[f49])).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.37/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_21,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_17,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_16,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_15,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_195,plain,
% 3.37/1.00      ( ~ l1_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_7,c_21,c_17,c_16,c_15]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_196,plain,
% 3.37/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_195]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_25,negated_conjecture,
% 3.37/1.00      ( m1_pre_topc(sK3,sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_965,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.37/1.00      | sK2 != X0
% 3.37/1.00      | sK3 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_196,c_25]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_966,plain,
% 3.37/1.00      ( ~ v2_pre_topc(sK2)
% 3.37/1.00      | v2_struct_0(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_965]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_29,negated_conjecture,
% 3.37/1.00      ( ~ v2_struct_0(sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_28,negated_conjecture,
% 3.37/1.00      ( v2_pre_topc(sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_27,negated_conjecture,
% 3.37/1.00      ( l1_pre_topc(sK2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_968,plain,
% 3.37/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_966,c_29,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3680,plain,
% 3.37/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_968]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_12,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2623,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2624,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2623]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2628,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2624,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3649,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2628]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4813,plain,
% 3.37/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3649]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6169,plain,
% 3.37/1.00      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3680,c_4813]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_973,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK2 != X1
% 3.37/1.00      | sK3 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_974,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_973]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_976,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.37/1.00      inference(global_propositional_subsumption,[status(thm)],[c_974,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3679,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_976]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4777,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3679]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_19,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2569,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2570,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2569]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2574,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2570,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3652,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | u1_struct_0(k6_tmap_1(sK2,X0_56)) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2574]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4810,plain,
% 3.37/1.00      ( u1_struct_0(k6_tmap_1(sK2,X0_56)) = u1_struct_0(sK2)
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3652]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5377,plain,
% 3.37/1.00      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4777,c_4810]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5380,plain,
% 3.37/1.00      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_5377,c_3680]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2641,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2642,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2641]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2646,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2642,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3648,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2646]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4814,plain,
% 3.37/1.00      ( k7_tmap_1(sK2,X0_56) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3648]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5560,plain,
% 3.37/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4777,c_4814]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6170,plain,
% 3.37/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_6169,c_5380,c_5560]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_32,plain,
% 3.37/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_975,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6930,plain,
% 3.37/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_6170,c_32,c_975]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_9,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.37/1.00      | ~ m1_pre_topc(X2,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.37/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_22,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1130,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X3)
% 3.37/1.00      | X3 != X1
% 3.37/1.00      | X3 != X2
% 3.37/1.00      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.37/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1131,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 3.37/1.00      | k9_tmap_1(X1,X1) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_1130]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2465,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 3.37/1.00      | k9_tmap_1(X1,X1) = X0
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_1131,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2466,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2465]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2470,plain,
% 3.37/1.00      ( ~ v1_funct_1(X0)
% 3.37/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2466,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2471,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | sK1(sK2,sK2,X0) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_2470]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3654,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0_56)
% 3.37/1.00      | sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0_56 ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2471]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4808,plain,
% 3.37/1.00      ( sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3654]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_809,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X2)
% 3.37/1.00      | X2 != X1
% 3.37/1.00      | X2 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_810,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.00      | ~ l1_pre_topc(X0) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_809]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3681,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 3.37/1.00      | ~ l1_pre_topc(X0_57) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_810]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4776,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 3.37/1.00      | l1_pre_topc(X0_57) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3681]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5378,plain,
% 3.37/1.00      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4776,c_4810]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_791,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | X1 != X0
% 3.37/1.00      | X1 != X2
% 3.37/1.00      | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_196,c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_792,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_791]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2183,plain,
% 3.37/1.00      ( ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 3.37/1.00      | sK2 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_792,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2184,plain,
% 3.37/1.00      ( ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2183]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_38,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_41,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK2,sK2)
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_53,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK2,sK2)
% 3.37/1.00      | v1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | v2_struct_0(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_56,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK2,sK2)
% 3.37/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | v2_struct_0(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_59,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK2,sK2)
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | v2_struct_0(sK2)
% 3.37/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_83,plain,
% 3.37/1.00      ( ~ m1_pre_topc(sK2,sK2)
% 3.37/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | v2_struct_0(sK2)
% 3.37/1.00      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2186,plain,
% 3.37/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2184,c_29,c_28,c_27,c_38,c_41,c_53,c_56,c_59,c_83]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3664,plain,
% 3.37/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2186]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5379,plain,
% 3.37/1.00      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2)
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_5378,c_3664]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5445,plain,
% 3.37/1.00      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 3.37/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5379,c_32]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6722,plain,
% 3.37/1.00      ( sK1(sK2,sK2,X0_56) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_4808,c_5445]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6935,plain,
% 3.37/1.00      ( sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_6930,c_6722]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5561,plain,
% 3.37/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4776,c_4814]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5002,plain,
% 3.37/1.00      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_3648]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5737,plain,
% 3.37/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK2)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_5561,c_27,c_38,c_41,c_5002]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_14,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1) ),
% 3.37/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2605,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2606,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,X0))
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2605]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2610,plain,
% 3.37/1.00      ( v1_funct_1(k7_tmap_1(sK2,X0))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2606,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2611,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,X0)) ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_2610]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3650,plain,
% 3.37/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,X0_56)) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2611]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4812,plain,
% 3.37/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,X0_56)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3650]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5373,plain,
% 3.37/1.00      ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_4776,c_4812]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_37,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_39,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_37]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_40,plain,
% 3.37/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.37/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_42,plain,
% 3.37/1.00      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_40]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5013,plain,
% 3.37/1.00      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_3650]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5014,plain,
% 3.37/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_5013]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5732,plain,
% 3.37/1.00      ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_5373,c_32,c_39,c_42,c_5014]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5739,plain,
% 3.37/1.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_5737,c_5732]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_13,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.37/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2249,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.37/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | sK2 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2250,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ l1_pre_topc(sK2) ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2249]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2254,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2250,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3662,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56)))
% 3.37/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2254]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4793,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))) = iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3662]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5930,plain,
% 3.37/1.00      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_3680,c_4793]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5931,plain,
% 3.37/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 3.37/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_5930,c_5380,c_5560]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_9679,plain,
% 3.37/1.00      ( sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_6935,c_32,c_975,c_5739,c_5931]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.37/1.00      | ~ m1_pre_topc(X2,X1)
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.37/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1100,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.37/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | ~ l1_pre_topc(X3)
% 3.37/1.00      | X3 != X1
% 3.37/1.00      | X3 != X2
% 3.37/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1101,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.37/1.00      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | v2_struct_0(X1)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k9_tmap_1(X1,X1) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_1100]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2492,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 3.37/1.00      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.00      | ~ v2_pre_topc(X1)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ l1_pre_topc(X1)
% 3.37/1.00      | k9_tmap_1(X1,X1) = X0
% 3.37/1.00      | sK2 != X1 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_1101,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2493,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2492]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2497,plain,
% 3.37/1.00      ( ~ v1_funct_1(X0)
% 3.37/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2493,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2498,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_2497]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3653,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.00      | ~ v1_funct_1(X0_56)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0_56 ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2498]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4809,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3653]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6825,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_4809,c_5445]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6934,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_6930,c_6825]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8857,plain,
% 3.37/1.00      ( m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_6934,c_32,c_975,c_5739,c_5931]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8858,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_8857]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8862,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_8858,c_4814]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2,plain,
% 3.37/1.00      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.37/1.00      | ~ v1_funct_2(X5,X2,X3)
% 3.37/1.00      | ~ v1_funct_2(X4,X0,X1)
% 3.37/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.37/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.00      | ~ v1_funct_1(X5)
% 3.37/1.00      | ~ v1_funct_1(X4)
% 3.37/1.00      | v1_xboole_0(X1)
% 3.37/1.00      | v1_xboole_0(X3) ),
% 3.37/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.37/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.00      | ~ m1_pre_topc(X1,X0)
% 3.37/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v1_funct_1(X2)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k9_tmap_1(X0,X1) = X2 ),
% 3.37/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_711,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.37/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v1_funct_1(X2)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | ~ l1_pre_topc(X3)
% 3.37/1.00      | X3 != X1
% 3.37/1.00      | X3 != X0
% 3.37/1.00      | k9_tmap_1(X0,X1) = X2 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_712,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 3.37/1.00      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.37/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v1_funct_1(X1)
% 3.37/1.00      | v2_struct_0(X0)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k9_tmap_1(X0,X0) = X1 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_711]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2191,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 3.37/1.00      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.37/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.37/1.00      | ~ v2_pre_topc(X0)
% 3.37/1.00      | ~ v1_funct_1(X1)
% 3.37/1.00      | ~ l1_pre_topc(X0)
% 3.37/1.00      | k9_tmap_1(X0,X0) = X1
% 3.37/1.00      | sK2 != X0 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_712,c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2192,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.37/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v2_pre_topc(sK2)
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ l1_pre_topc(sK2)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2191]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2196,plain,
% 3.37/1.00      ( ~ v1_funct_1(X0)
% 3.37/1.00      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.37/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_2192,c_28,c_27]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2197,plain,
% 3.37/1.00      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK2,X0)))
% 3.37/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0 ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_2196]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2907,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.00      | ~ v1_funct_2(X3,X4,X5)
% 3.37/1.00      | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ v1_funct_1(X3)
% 3.37/1.00      | ~ v1_funct_1(X6)
% 3.37/1.00      | v1_xboole_0(X5)
% 3.37/1.00      | v1_xboole_0(X2)
% 3.37/1.00      | X6 != X3
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X6
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X6)) != X3
% 3.37/1.00      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X6))) != X2
% 3.37/1.00      | u1_struct_0(k8_tmap_1(sK2,sK2)) != X5
% 3.37/1.00      | u1_struct_0(sK2) != X1
% 3.37/1.00      | u1_struct_0(sK2) != X4 ),
% 3.37/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_2197]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2908,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))
% 3.37/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))))
% 3.37/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0)
% 3.37/1.00      | ~ v1_funct_1(X1)
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1))))
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X1
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X1)) != X1 ),
% 3.37/1.00      inference(unflattening,[status(thm)],[c_2907]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_3646,plain,
% 3.37/1.00      ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))
% 3.37/1.00      | ~ v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))))
% 3.37/1.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.00      | ~ v1_funct_1(X0_56)
% 3.37/1.00      | ~ v1_funct_1(X1_56)
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X1_56))))
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X1_56
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X1_56)) != X1_56 ),
% 3.37/1.00      inference(subtyping,[status(esa)],[c_2908]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_4817,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
% 3.37/1.00      | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_funct_1(X1_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK2))) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3646]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5447,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
% 3.37/1.00      | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | v1_funct_1(X1_56) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.37/1.00      inference(demodulation,[status(thm)],[c_5445,c_4817]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_30,plain,
% 3.37/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_1,plain,
% 3.37/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_100,plain,
% 3.37/1.00      ( v2_struct_0(X0) = iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.37/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_102,plain,
% 3.37/1.00      ( v2_struct_0(sK2) = iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | l1_struct_0(sK2) != iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_100]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_0,plain,
% 3.37/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.37/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_103,plain,
% 3.37/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_105,plain,
% 3.37/1.00      ( l1_pre_topc(sK2) != iProver_top | l1_struct_0(sK2) = iProver_top ),
% 3.37/1.00      inference(instantiation,[status(thm)],[c_103]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6982,plain,
% 3.37/1.00      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_funct_1(X1_56) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = X0_56 ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_5447,c_30,c_32,c_102,c_105]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_6983,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = X0_56
% 3.37/1.00      | k7_tmap_1(sK2,sK1(sK2,sK2,X0_56)) != X0_56
% 3.37/1.00      | v1_funct_2(X1_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) != iProver_top
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | v1_funct_1(X1_56) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0_56)))) = iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_6982]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8868,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 3.37/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_8862,c_6983]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10991,plain,
% 3.37/1.00      ( v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_8868,c_32,c_975,c_5739,c_5931,c_6170]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10992,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_10991]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11000,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_9679,c_10992]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11001,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_11000,c_3664,c_5445]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8867,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_8862,c_4793]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_9917,plain,
% 3.37/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
% 3.37/1.00      | k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8867,c_8858]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_9918,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(renaming,[status(thm)],[c_9917]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8866,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | m1_subset_1(sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_8862,c_4813]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10174,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8866,c_8858]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_10998,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 3.37/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_10174,c_10992]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_11051,plain,
% 3.37/1.00      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 3.37/1.00      inference(global_propositional_subsumption,
% 3.37/1.00                [status(thm)],
% 3.37/1.00                [c_11001,c_5739,c_9918,c_10998]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11056,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_9679,c_11051]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11057,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_11056,c_3664,c_5445]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11060,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_11057,c_30,c_32,c_102,c_105]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.01      | ~ m1_pre_topc(X1,X0)
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_741,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | sK2 != X0
% 3.37/1.01      | sK3 != X1 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_742,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_741]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_744,plain,
% 3.37/1.01      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_742,c_29,c_28,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_745,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_744]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_983,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.37/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_976,c_745]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3058,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.37/1.01      | k9_tmap_1(sK2,sK2) = X0
% 3.37/1.01      | k9_tmap_1(sK2,sK3) != X0
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_983,c_2197]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3059,plain,
% 3.37/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.37/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_3058]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3642,plain,
% 3.37/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.37/1.01      | k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_3059]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4821,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_3642]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4840,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4821,c_3680]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6523,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 3.37/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4840,c_5380,c_5445,c_5560]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6524,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 3.37/1.01      inference(equality_resolution_simp,[status(thm)],[c_6523]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11069,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK2,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_11060,c_6524]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1160,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 3.37/1.01      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.01      | ~ v2_pre_topc(X1)
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | v2_struct_0(X1)
% 3.37/1.01      | ~ l1_pre_topc(X1)
% 3.37/1.01      | k9_tmap_1(X1,X2) = X0
% 3.37/1.01      | sK2 != X1
% 3.37/1.01      | sK3 != X2 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1161,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_1160]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1165,plain,
% 3.37/1.01      ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1161,c_29,c_28,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1166,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_1165]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3676,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_1(X0_56)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0_56 ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_1166]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4780,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = X0_56
% 3.37/1.01      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.37/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.01      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_3676]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6176,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = X0_56
% 3.37/1.01      | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.01      | v1_funct_1(X0_56) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4780,c_5380]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6937,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.01      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_6930,c_6176]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10218,plain,
% 3.37/1.01      ( m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_6937,c_32,c_975,c_5739,c_5931]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10219,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | m1_subset_1(sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_10218]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10224,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_10219,c_4814]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10225,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))))) = u1_struct_0(sK2) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_10219,c_4810]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_681,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | ~ l1_pre_topc(X2)
% 3.37/1.01      | X2 != X1
% 3.37/1.01      | X2 != X0 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_682,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_681]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2218,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))),k9_tmap_1(X0,X0),k7_tmap_1(X0,u1_struct_0(X0)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X0),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X0))
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | sK2 != X0 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_682,c_29]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2219,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | ~ l1_pre_topc(sK2) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_2218]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_684,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_682]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2221,plain,
% 3.37/1.01      ( ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2))) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_2219,c_29,c_28,c_27,c_38,c_41,c_684]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2222,plain,
% 3.37/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))),k9_tmap_1(sK2,sK2),k7_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2)) ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_2221]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_764,plain,
% 3.37/1.01      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 3.37/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.37/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ v1_funct_1(X2)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | k9_tmap_1(X0,X1) = X2
% 3.37/1.01      | sK2 != X0
% 3.37/1.01      | sK3 != X1 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_765,plain,
% 3.37/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.37/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_764]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_769,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_765,c_29,c_28,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_770,plain,
% 3.37/1.01      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
% 3.37/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0 ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_769]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2943,plain,
% 3.37/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | k9_tmap_1(sK2,sK2) != X0
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = X0
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,X0)) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_2222,c_770]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2944,plain,
% 3.37/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_2943]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3645,plain,
% 3.37/1.01      ( ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))
% 3.37/1.01      | ~ v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2)))))
% 3.37/1.01      | ~ m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.37/1.01      | ~ v1_funct_1(k9_tmap_1(sK2,sK2))
% 3.37/1.01      | k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_2944]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4818,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k9_tmap_1(sK2,sK2)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2)))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_3645]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4839,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k7_tmap_1(sK2,u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK2))
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))) != iProver_top
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK2))))) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4818,c_3664]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6436,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
% 3.37/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4839,c_5380,c_5445,c_5737]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6437,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK2) = k9_tmap_1(sK2,sK3)
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k9_tmap_1(sK2,sK2)))) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k9_tmap_1(sK2,sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k9_tmap_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k9_tmap_1(sK2,sK2)) != iProver_top ),
% 3.37/1.01      inference(equality_resolution_simp,[status(thm)],[c_6436]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11070,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | k7_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2)))) != k6_partfun1(u1_struct_0(sK2))
% 3.37/1.01      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k6_partfun1(u1_struct_0(sK2))))) != u1_struct_0(sK2)
% 3.37/1.01      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.37/1.01      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.37/1.01      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_11060,c_6437]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11283,plain,
% 3.37/1.01      ( k9_tmap_1(sK2,sK3) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_11069,c_32,c_975,c_5739,c_5931,c_6170,c_10224,c_10225,
% 3.37/1.01                 c_11070]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_20,plain,
% 3.37/1.01      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.37/1.01      | ~ m1_pre_topc(X0,X1)
% 3.37/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/1.01      | ~ v2_pre_topc(X1)
% 3.37/1.01      | v2_struct_0(X1)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X1) ),
% 3.37/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_176,plain,
% 3.37/1.01      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.01      | ~ m1_pre_topc(X0,X1)
% 3.37/1.01      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.37/1.01      | ~ v2_pre_topc(X1)
% 3.37/1.01      | v2_struct_0(X1)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X1) ),
% 3.37/1.01      inference(global_propositional_subsumption,[status(thm)],[c_20,c_21]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_177,plain,
% 3.37/1.01      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.37/1.01      | ~ m1_pre_topc(X0,X1)
% 3.37/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.01      | ~ v2_pre_topc(X1)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | v2_struct_0(X1)
% 3.37/1.01      | ~ l1_pre_topc(X1) ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_176]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_23,negated_conjecture,
% 3.37/1.01      ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
% 3.37/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_372,plain,
% 3.37/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.37/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.01      | ~ v2_pre_topc(X1)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | v2_struct_0(X1)
% 3.37/1.01      | ~ l1_pre_topc(X1)
% 3.37/1.01      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK2,sK3)
% 3.37/1.01      | sK4 != X2
% 3.37/1.01      | sK3 != X0 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_177,c_23]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_373,plain,
% 3.37/1.01      ( ~ m1_pre_topc(sK3,X0)
% 3.37/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | v2_struct_0(sK3)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_372]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_26,negated_conjecture,
% 3.37/1.01      ( ~ v2_struct_0(sK3) ),
% 3.37/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_24,negated_conjecture,
% 3.37/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_377,plain,
% 3.37/1.01      ( v2_struct_0(X0)
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | ~ m1_pre_topc(sK3,X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_373,c_26,c_24]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_378,plain,
% 3.37/1.01      ( ~ m1_pre_topc(sK3,X0)
% 3.37/1.01      | ~ v2_pre_topc(X0)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_377]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1234,plain,
% 3.37/1.01      ( ~ v2_pre_topc(X0)
% 3.37/1.01      | v2_struct_0(X0)
% 3.37/1.01      | ~ l1_pre_topc(X0)
% 3.37/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.37/1.01      | sK2 != X0
% 3.37/1.01      | sK3 != sK3 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_378]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1235,plain,
% 3.37/1.01      ( ~ v2_pre_topc(sK2)
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2)
% 3.37/1.01      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_1234]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_380,plain,
% 3.37/1.01      ( ~ m1_pre_topc(sK3,sK2)
% 3.37/1.01      | ~ v2_pre_topc(sK2)
% 3.37/1.01      | v2_struct_0(sK2)
% 3.37/1.01      | ~ l1_pre_topc(sK2)
% 3.37/1.01      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.37/1.01      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_378]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1237,plain,
% 3.37/1.01      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1235,c_29,c_28,c_27,c_25,c_380,c_966]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3673,plain,
% 3.37/1.01      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_1237]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4838,plain,
% 3.37/1.01      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_3673,c_3680]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6111,plain,
% 3.37/1.01      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4838,c_5560]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11291,plain,
% 3.37/1.01      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_11283,c_6111]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11292,plain,
% 3.37/1.01      ( $false ),
% 3.37/1.01      inference(equality_resolution_simp,[status(thm)],[c_11291]) ).
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  ------                               Statistics
% 3.37/1.01  
% 3.37/1.01  ------ General
% 3.37/1.01  
% 3.37/1.01  abstr_ref_over_cycles:                  0
% 3.37/1.01  abstr_ref_under_cycles:                 0
% 3.37/1.01  gc_basic_clause_elim:                   0
% 3.37/1.01  forced_gc_time:                         0
% 3.37/1.01  parsing_time:                           0.029
% 3.37/1.01  unif_index_cands_time:                  0.
% 3.37/1.01  unif_index_add_time:                    0.
% 3.37/1.01  orderings_time:                         0.
% 3.37/1.01  out_proof_time:                         0.022
% 3.37/1.01  total_time:                             0.495
% 3.37/1.01  num_of_symbols:                         75
% 3.37/1.01  num_of_terms:                           10285
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing
% 3.37/1.01  
% 3.37/1.01  num_of_splits:                          9
% 3.37/1.01  num_of_split_atoms:                     9
% 3.37/1.01  num_of_reused_defs:                     0
% 3.37/1.01  num_eq_ax_congr_red:                    12
% 3.37/1.01  num_of_sem_filtered_clauses:            8
% 3.37/1.01  num_of_subtypes:                        4
% 3.37/1.01  monotx_restored_types:                  0
% 3.37/1.01  sat_num_of_epr_types:                   0
% 3.37/1.01  sat_num_of_non_cyclic_types:            0
% 3.37/1.01  sat_guarded_non_collapsed_types:        1
% 3.37/1.01  num_pure_diseq_elim:                    0
% 3.37/1.01  simp_replaced_by:                       0
% 3.37/1.01  res_preprocessed:                       222
% 3.37/1.01  prep_upred:                             0
% 3.37/1.01  prep_unflattend:                        175
% 3.37/1.01  smt_new_axioms:                         0
% 3.37/1.01  pred_elim_cands:                        12
% 3.37/1.01  pred_elim:                              6
% 3.37/1.01  pred_elim_cl:                           -33
% 3.37/1.01  pred_elim_cycles:                       11
% 3.37/1.01  merged_defs:                            0
% 3.37/1.01  merged_defs_ncl:                        0
% 3.37/1.01  bin_hyper_res:                          0
% 3.37/1.01  prep_cycles:                            3
% 3.37/1.01  pred_elim_time:                         0.167
% 3.37/1.01  splitting_time:                         0.
% 3.37/1.01  sem_filter_time:                        0.
% 3.37/1.01  monotx_time:                            0.
% 3.37/1.01  subtype_inf_time:                       0.001
% 3.37/1.01  
% 3.37/1.01  ------ Problem properties
% 3.37/1.01  
% 3.37/1.01  clauses:                                72
% 3.37/1.01  conjectures:                            3
% 3.37/1.01  epr:                                    10
% 3.37/1.01  horn:                                   50
% 3.37/1.01  ground:                                 50
% 3.37/1.01  unary:                                  12
% 3.37/1.01  binary:                                 14
% 3.37/1.01  lits:                                   275
% 3.37/1.01  lits_eq:                                85
% 3.37/1.01  fd_pure:                                0
% 3.37/1.01  fd_pseudo:                              0
% 3.37/1.01  fd_cond:                                9
% 3.37/1.01  fd_pseudo_cond:                         0
% 3.37/1.01  ac_symbols:                             0
% 3.37/1.01  
% 3.37/1.01  ------ Propositional Solver
% 3.37/1.01  
% 3.37/1.01  prop_solver_calls:                      27
% 3.37/1.01  prop_fast_solver_calls:                 3372
% 3.37/1.01  smt_solver_calls:                       0
% 3.37/1.01  smt_fast_solver_calls:                  0
% 3.37/1.01  prop_num_of_clauses:                    3228
% 3.37/1.01  prop_preprocess_simplified:             9546
% 3.37/1.01  prop_fo_subsumed:                       185
% 3.37/1.01  prop_solver_time:                       0.
% 3.37/1.01  smt_solver_time:                        0.
% 3.37/1.01  smt_fast_solver_time:                   0.
% 3.37/1.01  prop_fast_solver_time:                  0.
% 3.37/1.01  prop_unsat_core_time:                   0.
% 3.37/1.01  
% 3.37/1.01  ------ QBF
% 3.37/1.01  
% 3.37/1.01  qbf_q_res:                              0
% 3.37/1.01  qbf_num_tautologies:                    0
% 3.37/1.01  qbf_prep_cycles:                        0
% 3.37/1.01  
% 3.37/1.01  ------ BMC1
% 3.37/1.01  
% 3.37/1.01  bmc1_current_bound:                     -1
% 3.37/1.01  bmc1_last_solved_bound:                 -1
% 3.37/1.01  bmc1_unsat_core_size:                   -1
% 3.37/1.01  bmc1_unsat_core_parents_size:           -1
% 3.37/1.01  bmc1_merge_next_fun:                    0
% 3.37/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation
% 3.37/1.01  
% 3.37/1.01  inst_num_of_clauses:                    1103
% 3.37/1.01  inst_num_in_passive:                    233
% 3.37/1.01  inst_num_in_active:                     678
% 3.37/1.01  inst_num_in_unprocessed:                192
% 3.37/1.01  inst_num_of_loops:                      760
% 3.37/1.01  inst_num_of_learning_restarts:          0
% 3.37/1.01  inst_num_moves_active_passive:          75
% 3.37/1.01  inst_lit_activity:                      0
% 3.37/1.01  inst_lit_activity_moves:                0
% 3.37/1.01  inst_num_tautologies:                   0
% 3.37/1.01  inst_num_prop_implied:                  0
% 3.37/1.01  inst_num_existing_simplified:           0
% 3.37/1.01  inst_num_eq_res_simplified:             0
% 3.37/1.01  inst_num_child_elim:                    0
% 3.37/1.01  inst_num_of_dismatching_blockings:      1166
% 3.37/1.01  inst_num_of_non_proper_insts:           1357
% 3.37/1.01  inst_num_of_duplicates:                 0
% 3.37/1.01  inst_inst_num_from_inst_to_res:         0
% 3.37/1.01  inst_dismatching_checking_time:         0.
% 3.37/1.01  
% 3.37/1.01  ------ Resolution
% 3.37/1.01  
% 3.37/1.01  res_num_of_clauses:                     0
% 3.37/1.01  res_num_in_passive:                     0
% 3.37/1.01  res_num_in_active:                      0
% 3.37/1.01  res_num_of_loops:                       225
% 3.37/1.01  res_forward_subset_subsumed:            113
% 3.37/1.01  res_backward_subset_subsumed:           0
% 3.37/1.01  res_forward_subsumed:                   0
% 3.37/1.01  res_backward_subsumed:                  0
% 3.37/1.01  res_forward_subsumption_resolution:     14
% 3.37/1.01  res_backward_subsumption_resolution:    1
% 3.37/1.01  res_clause_to_clause_subsumption:       505
% 3.37/1.01  res_orphan_elimination:                 0
% 3.37/1.01  res_tautology_del:                      267
% 3.37/1.01  res_num_eq_res_simplified:              0
% 3.37/1.01  res_num_sel_changes:                    0
% 3.37/1.01  res_moves_from_active_to_pass:          0
% 3.37/1.01  
% 3.37/1.01  ------ Superposition
% 3.37/1.01  
% 3.37/1.01  sup_time_total:                         0.
% 3.37/1.01  sup_time_generating:                    0.
% 3.37/1.01  sup_time_sim_full:                      0.
% 3.37/1.01  sup_time_sim_immed:                     0.
% 3.37/1.01  
% 3.37/1.01  sup_num_of_clauses:                     129
% 3.37/1.01  sup_num_in_active:                      107
% 3.37/1.01  sup_num_in_passive:                     22
% 3.37/1.01  sup_num_of_loops:                       150
% 3.37/1.01  sup_fw_superposition:                   81
% 3.37/1.01  sup_bw_superposition:                   107
% 3.37/1.01  sup_immediate_simplified:               82
% 3.37/1.01  sup_given_eliminated:                   0
% 3.37/1.01  comparisons_done:                       0
% 3.37/1.01  comparisons_avoided:                    88
% 3.37/1.01  
% 3.37/1.01  ------ Simplifications
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  sim_fw_subset_subsumed:                 30
% 3.37/1.01  sim_bw_subset_subsumed:                 28
% 3.37/1.01  sim_fw_subsumed:                        13
% 3.37/1.01  sim_bw_subsumed:                        7
% 3.37/1.01  sim_fw_subsumption_res:                 0
% 3.37/1.01  sim_bw_subsumption_res:                 0
% 3.37/1.01  sim_tautology_del:                      2
% 3.37/1.01  sim_eq_tautology_del:                   6
% 3.37/1.01  sim_eq_res_simp:                        4
% 3.37/1.01  sim_fw_demodulated:                     0
% 3.37/1.01  sim_bw_demodulated:                     19
% 3.37/1.01  sim_light_normalised:                   68
% 3.37/1.01  sim_joinable_taut:                      0
% 3.37/1.01  sim_joinable_simp:                      0
% 3.37/1.01  sim_ac_normalised:                      0
% 3.37/1.01  sim_smt_subsumption:                    0
% 3.37/1.01  
%------------------------------------------------------------------------------
