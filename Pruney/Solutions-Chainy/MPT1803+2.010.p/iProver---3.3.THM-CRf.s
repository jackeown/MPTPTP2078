%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:10 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  230 (1848 expanded)
%              Number of clauses        :  130 ( 484 expanded)
%              Number of leaves         :   26 ( 498 expanded)
%              Depth                    :   24
%              Number of atoms          : 1286 (11453 expanded)
%              Number of equality atoms :  338 (1251 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK6)
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK5,k8_tmap_1(X0,sK5),k2_tmap_1(X0,k8_tmap_1(X0,sK5),k9_tmap_1(X0,sK5),sK5),X2)
            & m1_subset_1(X2,u1_struct_0(sK5)) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
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
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK4,X1),k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6)
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f45,f64,f63,f62])).

fof(f104,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f108])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f101,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f110,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f110])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f52])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f50])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    ~ r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1767,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_2579,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_268,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_33,c_25,c_24,c_23])).

cnf(c_269,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_1761,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | v2_struct_0(X1_60)
    | ~ v2_pre_topc(X1_60)
    | ~ l1_pre_topc(X1_60)
    | k6_tmap_1(X1_60,u1_struct_0(X0_60)) = k8_tmap_1(X1_60,X0_60) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_2585,plain,
    ( k6_tmap_1(X0_60,u1_struct_0(X1_60)) = k8_tmap_1(X0_60,X1_60)
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_4353,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5)
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_2585])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3067,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_4356,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4353,c_40,c_39,c_38,c_36,c_3067])).

cnf(c_17,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_27,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_258,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_27])).

cnf(c_1762,plain,
    ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60)))
    | ~ m1_pre_topc(X1_60,X0_60)
    | ~ m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))))
    | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60)))
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ v1_funct_1(k9_tmap_1(X0_60,X1_60))
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_2584,plain,
    ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))))) != iProver_top
    | m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v1_funct_1(k9_tmap_1(X0_60,X1_60)) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1772,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | v2_struct_0(X1_60)
    | ~ v2_pre_topc(X1_60)
    | v1_funct_1(k9_tmap_1(X1_60,X0_60))
    | ~ l1_pre_topc(X1_60) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2574,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | v2_struct_0(X1_60) = iProver_top
    | v2_pre_topc(X1_60) != iProver_top
    | v1_funct_1(k9_tmap_1(X1_60,X0_60)) = iProver_top
    | l1_pre_topc(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_1769,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60)))
    | ~ l1_pre_topc(X1_60) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_2577,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60))) = iProver_top
    | l1_pre_topc(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1774,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | m1_subset_1(k9_tmap_1(X1_60,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_60),u1_struct_0(k8_tmap_1(X1_60,X0_60)))))
    | v2_struct_0(X1_60)
    | ~ v2_pre_topc(X1_60)
    | ~ l1_pre_topc(X1_60) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2572,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | m1_subset_1(k9_tmap_1(X1_60,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_60),u1_struct_0(k8_tmap_1(X1_60,X0_60))))) = iProver_top
    | v2_struct_0(X1_60) = iProver_top
    | v2_pre_topc(X1_60) != iProver_top
    | l1_pre_topc(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_2924,plain,
    ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2584,c_2574,c_2577,c_2572])).

cnf(c_6603,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4356,c_2924])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1770,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ l1_pre_topc(X0_60)
    | u1_struct_0(k6_tmap_1(X0_60,X0_61)) = u1_struct_0(X0_60) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2576,plain,
    ( u1_struct_0(k6_tmap_1(X0_60,X0_61)) = u1_struct_0(X0_60)
    | m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1770])).

cnf(c_4183,plain,
    ( u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))) = u1_struct_0(X0_60)
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_2576])).

cnf(c_4543,plain,
    ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_4183])).

cnf(c_4544,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4543,c_4356])).

cnf(c_41,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4547,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4544,c_41,c_42,c_43])).

cnf(c_6648,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6603,c_4547])).

cnf(c_45,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6887,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6648,c_41,c_42,c_43,c_45])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1787,plain,
    ( ~ r1_funct_2(X0_61,X1_61,X2_61,X3_61,X4_61,X5_61)
    | ~ v1_funct_2(X5_61,X2_61,X3_61)
    | ~ v1_funct_2(X4_61,X0_61,X1_61)
    | ~ m1_subset_1(X5_61,k1_zfmisc_1(k2_zfmisc_1(X2_61,X3_61)))
    | ~ m1_subset_1(X4_61,k1_zfmisc_1(k2_zfmisc_1(X0_61,X1_61)))
    | ~ v1_funct_1(X5_61)
    | ~ v1_funct_1(X4_61)
    | v1_xboole_0(X1_61)
    | v1_xboole_0(X3_61)
    | X4_61 = X5_61 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2559,plain,
    ( X0_61 = X1_61
    | r1_funct_2(X2_61,X3_61,X4_61,X5_61,X0_61,X1_61) != iProver_top
    | v1_funct_2(X0_61,X2_61,X3_61) != iProver_top
    | v1_funct_2(X1_61,X4_61,X5_61) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(X2_61,X3_61))) != iProver_top
    | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(X4_61,X5_61))) != iProver_top
    | v1_funct_1(X0_61) != iProver_top
    | v1_funct_1(X1_61) != iProver_top
    | v1_xboole_0(X5_61) = iProver_top
    | v1_xboole_0(X3_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_6892,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK4,sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_2559])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1780,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
    | m1_subset_1(k7_tmap_1(X0_60,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61)))))
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2566,plain,
    ( m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_60,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61))))) = iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_5059,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4356,c_2566])).

cnf(c_5078,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5059,c_4547])).

cnf(c_4915,plain,
    ( m1_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4547,c_2572])).

cnf(c_1773,plain,
    ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))
    | ~ m1_pre_topc(X1_60,X0_60)
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2573,plain,
    ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))) = iProver_top
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1773])).

cnf(c_4560,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4547,c_2573])).

cnf(c_21,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1779,plain,
    ( v1_funct_2(k7_tmap_1(X0_60,X0_61),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2567,plain,
    ( v1_funct_2(k7_tmap_1(X0_60,X0_61),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61))) = iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_4360,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4356,c_2567])).

cnf(c_3038,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_3039,plain,
    ( m1_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3038])).

cnf(c_4467,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4360,c_41,c_42,c_43,c_45,c_3039])).

cnf(c_4550,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4547,c_4467])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1795,plain,
    ( r2_hidden(sK0(X0_61),X0_61)
    | v1_xboole_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2551,plain,
    ( r2_hidden(sK0(X0_61),X0_61) = iProver_top
    | v1_xboole_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1795])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1790,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(X1_61))
    | ~ r2_hidden(X0_64,X0_61)
    | ~ v1_xboole_0(X1_61) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2556,plain,
    ( m1_subset_1(X0_61,k1_zfmisc_1(X1_61)) != iProver_top
    | r2_hidden(X0_64,X0_61) != iProver_top
    | v1_xboole_0(X1_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_3551,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | r2_hidden(X0_64,u1_struct_0(X0_60)) != iProver_top
    | l1_pre_topc(X1_60) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_60)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_2556])).

cnf(c_3713,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | l1_pre_topc(X1_60) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_60)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_60)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_3551])).

cnf(c_3810,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_3713])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1792,plain,
    ( r1_xboole_0(X0_61,X1_61)
    | r2_hidden(sK1(X0_61,X1_61),X1_61) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2554,plain,
    ( r1_xboole_0(X0_61,X1_61) = iProver_top
    | r2_hidden(sK1(X0_61,X1_61),X1_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1794,plain,
    ( ~ r2_hidden(X0_64,X0_61)
    | ~ v1_xboole_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2552,plain,
    ( r2_hidden(X0_64,X0_61) != iProver_top
    | v1_xboole_0(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_3144,plain,
    ( r1_xboole_0(X0_61,X1_61) = iProver_top
    | v1_xboole_0(X1_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_2552])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0),X3)
    | ~ r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_510,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k8_tmap_1(X2,X0),k9_tmap_1(X2,X0),X1) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X2,X0) != k8_tmap_1(sK4,sK5)
    | sK6 != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_511,plain,
    ( ~ r1_tsep_1(X0,sK5)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_515,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,sK5)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_37,c_35])).

cnf(c_516,plain,
    ( ~ r1_tsep_1(X0,sK5)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_567,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | X0 != X2
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_516])).

cnf(c_568,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK5)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_572,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_struct_0(sK5)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_7,c_6])).

cnf(c_573,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(sK5)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_620,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_573])).

cnf(c_621,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_645,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_621,c_7])).

cnf(c_1759,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | ~ m1_pre_topc(sK5,X1_60)
    | ~ r1_xboole_0(u1_struct_0(X0_60),u1_struct_0(sK5))
    | v2_struct_0(X0_60)
    | v2_struct_0(X1_60)
    | ~ v2_pre_topc(X1_60)
    | ~ l1_pre_topc(X1_60)
    | k2_tmap_1(X1_60,k8_tmap_1(X1_60,X0_60),k9_tmap_1(X1_60,X0_60),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X1_60,X0_60) != k8_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_645])).

cnf(c_2587,plain,
    ( k2_tmap_1(X0_60,k8_tmap_1(X0_60,X1_60),k9_tmap_1(X0_60,X1_60),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k8_tmap_1(X0_60,X1_60) != k8_tmap_1(sK4,sK5)
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | m1_pre_topc(sK5,X0_60) != iProver_top
    | r1_xboole_0(u1_struct_0(X1_60),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | v2_struct_0(X1_60) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_3100,plain,
    ( k8_tmap_1(sK4,sK5) != k8_tmap_1(sK4,sK5)
    | m1_pre_topc(sK5,sK4) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2587])).

cnf(c_3220,plain,
    ( m1_pre_topc(sK5,sK4) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3100])).

cnf(c_44,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3222,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_41,c_42,c_43,c_44,c_45])).

cnf(c_3271,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3144,c_3222])).

cnf(c_1825,plain,
    ( k2_tmap_1(X0_60,X1_60,X0_61,X2_60) = k2_tmap_1(X3_60,X4_60,X1_61,X5_60)
    | X0_61 != X1_61
    | X0_60 != X3_60
    | X1_60 != X4_60
    | X2_60 != X5_60 ),
    theory(equality)).

cnf(c_3263,plain,
    ( k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK5)),k7_tmap_1(X0_60,u1_struct_0(sK5)),sK5) = k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k7_tmap_1(X0_60,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | X0_60 != sK4
    | k6_tmap_1(X0_60,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_3264,plain,
    ( k2_tmap_1(sK4,k6_tmap_1(sK4,u1_struct_0(sK5)),k7_tmap_1(sK4,u1_struct_0(sK5)),sK5) = k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
    | sK4 != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_1797,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_3256,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | v1_funct_1(k7_tmap_1(X0_60,X0_61))
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3151,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_3152,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3151])).

cnf(c_3041,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k9_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_3042,plain,
    ( m1_pre_topc(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k9_tmap_1(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3041])).

cnf(c_31,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_33])).

cnf(c_239,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_480,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK4,sK5)
    | sK6 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_34])).

cnf(c_481,plain,
    ( ~ m1_pre_topc(sK5,X0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_485,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(sK5,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_37,c_35])).

cnf(c_486,plain,
    ( ~ m1_pre_topc(sK5,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_485])).

cnf(c_1760,plain,
    ( ~ m1_pre_topc(sK5,X0_60)
    | v2_struct_0(X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ l1_pre_topc(X0_60)
    | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK5)),k7_tmap_1(X0_60,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(X0_60,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_1922,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | k2_tmap_1(sK4,k6_tmap_1(sK4,u1_struct_0(sK5)),k7_tmap_1(sK4,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
    | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_1847,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6892,c_5078,c_4915,c_4560,c_4550,c_3810,c_3271,c_3264,c_3256,c_3152,c_3067,c_3042,c_3039,c_1922,c_1847,c_45,c_36,c_43,c_38,c_42,c_39,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.92/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.01  
% 1.92/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.92/1.01  
% 1.92/1.01  ------  iProver source info
% 1.92/1.01  
% 1.92/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.92/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.92/1.01  git: non_committed_changes: false
% 1.92/1.01  git: last_make_outside_of_git: false
% 1.92/1.01  
% 1.92/1.01  ------ 
% 1.92/1.01  
% 1.92/1.01  ------ Input Options
% 1.92/1.01  
% 1.92/1.01  --out_options                           all
% 1.92/1.01  --tptp_safe_out                         true
% 1.92/1.01  --problem_path                          ""
% 1.92/1.01  --include_path                          ""
% 1.92/1.01  --clausifier                            res/vclausify_rel
% 1.92/1.01  --clausifier_options                    --mode clausify
% 1.92/1.01  --stdin                                 false
% 1.92/1.01  --stats_out                             all
% 1.92/1.01  
% 1.92/1.01  ------ General Options
% 1.92/1.01  
% 1.92/1.01  --fof                                   false
% 1.92/1.01  --time_out_real                         305.
% 1.92/1.01  --time_out_virtual                      -1.
% 1.92/1.01  --symbol_type_check                     false
% 1.92/1.01  --clausify_out                          false
% 1.92/1.01  --sig_cnt_out                           false
% 1.92/1.01  --trig_cnt_out                          false
% 1.92/1.01  --trig_cnt_out_tolerance                1.
% 1.92/1.01  --trig_cnt_out_sk_spl                   false
% 1.92/1.01  --abstr_cl_out                          false
% 1.92/1.01  
% 1.92/1.01  ------ Global Options
% 1.92/1.01  
% 1.92/1.01  --schedule                              default
% 1.92/1.01  --add_important_lit                     false
% 1.92/1.01  --prop_solver_per_cl                    1000
% 1.92/1.01  --min_unsat_core                        false
% 1.92/1.01  --soft_assumptions                      false
% 1.92/1.01  --soft_lemma_size                       3
% 1.92/1.01  --prop_impl_unit_size                   0
% 1.92/1.01  --prop_impl_unit                        []
% 1.92/1.01  --share_sel_clauses                     true
% 1.92/1.01  --reset_solvers                         false
% 1.92/1.01  --bc_imp_inh                            [conj_cone]
% 1.92/1.01  --conj_cone_tolerance                   3.
% 1.92/1.01  --extra_neg_conj                        none
% 1.92/1.01  --large_theory_mode                     true
% 1.92/1.01  --prolific_symb_bound                   200
% 1.92/1.01  --lt_threshold                          2000
% 1.92/1.01  --clause_weak_htbl                      true
% 1.92/1.01  --gc_record_bc_elim                     false
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing Options
% 1.92/1.01  
% 1.92/1.01  --preprocessing_flag                    true
% 1.92/1.01  --time_out_prep_mult                    0.1
% 1.92/1.01  --splitting_mode                        input
% 1.92/1.01  --splitting_grd                         true
% 1.92/1.01  --splitting_cvd                         false
% 1.92/1.01  --splitting_cvd_svl                     false
% 1.92/1.01  --splitting_nvd                         32
% 1.92/1.01  --sub_typing                            true
% 1.92/1.01  --prep_gs_sim                           true
% 1.92/1.01  --prep_unflatten                        true
% 1.92/1.01  --prep_res_sim                          true
% 1.92/1.01  --prep_upred                            true
% 1.92/1.01  --prep_sem_filter                       exhaustive
% 1.92/1.01  --prep_sem_filter_out                   false
% 1.92/1.01  --pred_elim                             true
% 1.92/1.01  --res_sim_input                         true
% 1.92/1.01  --eq_ax_congr_red                       true
% 1.92/1.01  --pure_diseq_elim                       true
% 1.92/1.01  --brand_transform                       false
% 1.92/1.01  --non_eq_to_eq                          false
% 1.92/1.01  --prep_def_merge                        true
% 1.92/1.01  --prep_def_merge_prop_impl              false
% 1.92/1.01  --prep_def_merge_mbd                    true
% 1.92/1.01  --prep_def_merge_tr_red                 false
% 1.92/1.01  --prep_def_merge_tr_cl                  false
% 1.92/1.01  --smt_preprocessing                     true
% 1.92/1.01  --smt_ac_axioms                         fast
% 1.92/1.01  --preprocessed_out                      false
% 1.92/1.01  --preprocessed_stats                    false
% 1.92/1.01  
% 1.92/1.01  ------ Abstraction refinement Options
% 1.92/1.01  
% 1.92/1.01  --abstr_ref                             []
% 1.92/1.01  --abstr_ref_prep                        false
% 1.92/1.01  --abstr_ref_until_sat                   false
% 1.92/1.01  --abstr_ref_sig_restrict                funpre
% 1.92/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/1.01  --abstr_ref_under                       []
% 1.92/1.01  
% 1.92/1.01  ------ SAT Options
% 1.92/1.01  
% 1.92/1.01  --sat_mode                              false
% 1.92/1.01  --sat_fm_restart_options                ""
% 1.92/1.01  --sat_gr_def                            false
% 1.92/1.01  --sat_epr_types                         true
% 1.92/1.01  --sat_non_cyclic_types                  false
% 1.92/1.01  --sat_finite_models                     false
% 1.92/1.01  --sat_fm_lemmas                         false
% 1.92/1.01  --sat_fm_prep                           false
% 1.92/1.01  --sat_fm_uc_incr                        true
% 1.92/1.01  --sat_out_model                         small
% 1.92/1.01  --sat_out_clauses                       false
% 1.92/1.01  
% 1.92/1.01  ------ QBF Options
% 1.92/1.01  
% 1.92/1.01  --qbf_mode                              false
% 1.92/1.01  --qbf_elim_univ                         false
% 1.92/1.01  --qbf_dom_inst                          none
% 1.92/1.01  --qbf_dom_pre_inst                      false
% 1.92/1.01  --qbf_sk_in                             false
% 1.92/1.01  --qbf_pred_elim                         true
% 1.92/1.01  --qbf_split                             512
% 1.92/1.01  
% 1.92/1.01  ------ BMC1 Options
% 1.92/1.01  
% 1.92/1.01  --bmc1_incremental                      false
% 1.92/1.01  --bmc1_axioms                           reachable_all
% 1.92/1.01  --bmc1_min_bound                        0
% 1.92/1.01  --bmc1_max_bound                        -1
% 1.92/1.01  --bmc1_max_bound_default                -1
% 1.92/1.01  --bmc1_symbol_reachability              true
% 1.92/1.01  --bmc1_property_lemmas                  false
% 1.92/1.01  --bmc1_k_induction                      false
% 1.92/1.01  --bmc1_non_equiv_states                 false
% 1.92/1.01  --bmc1_deadlock                         false
% 1.92/1.01  --bmc1_ucm                              false
% 1.92/1.01  --bmc1_add_unsat_core                   none
% 1.92/1.01  --bmc1_unsat_core_children              false
% 1.92/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/1.01  --bmc1_out_stat                         full
% 1.92/1.01  --bmc1_ground_init                      false
% 1.92/1.01  --bmc1_pre_inst_next_state              false
% 1.92/1.01  --bmc1_pre_inst_state                   false
% 1.92/1.01  --bmc1_pre_inst_reach_state             false
% 1.92/1.01  --bmc1_out_unsat_core                   false
% 1.92/1.01  --bmc1_aig_witness_out                  false
% 1.92/1.01  --bmc1_verbose                          false
% 1.92/1.01  --bmc1_dump_clauses_tptp                false
% 1.92/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.92/1.01  --bmc1_dump_file                        -
% 1.92/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.92/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.92/1.01  --bmc1_ucm_extend_mode                  1
% 1.92/1.01  --bmc1_ucm_init_mode                    2
% 1.92/1.01  --bmc1_ucm_cone_mode                    none
% 1.92/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.92/1.01  --bmc1_ucm_relax_model                  4
% 1.92/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.92/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/1.01  --bmc1_ucm_layered_model                none
% 1.92/1.01  --bmc1_ucm_max_lemma_size               10
% 1.92/1.01  
% 1.92/1.01  ------ AIG Options
% 1.92/1.01  
% 1.92/1.01  --aig_mode                              false
% 1.92/1.01  
% 1.92/1.01  ------ Instantiation Options
% 1.92/1.01  
% 1.92/1.01  --instantiation_flag                    true
% 1.92/1.01  --inst_sos_flag                         false
% 1.92/1.01  --inst_sos_phase                        true
% 1.92/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/1.01  --inst_lit_sel_side                     num_symb
% 1.92/1.01  --inst_solver_per_active                1400
% 1.92/1.01  --inst_solver_calls_frac                1.
% 1.92/1.01  --inst_passive_queue_type               priority_queues
% 1.92/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/1.01  --inst_passive_queues_freq              [25;2]
% 1.92/1.01  --inst_dismatching                      true
% 1.92/1.01  --inst_eager_unprocessed_to_passive     true
% 1.92/1.01  --inst_prop_sim_given                   true
% 1.92/1.01  --inst_prop_sim_new                     false
% 1.92/1.01  --inst_subs_new                         false
% 1.92/1.01  --inst_eq_res_simp                      false
% 1.92/1.01  --inst_subs_given                       false
% 1.92/1.01  --inst_orphan_elimination               true
% 1.92/1.01  --inst_learning_loop_flag               true
% 1.92/1.01  --inst_learning_start                   3000
% 1.92/1.01  --inst_learning_factor                  2
% 1.92/1.01  --inst_start_prop_sim_after_learn       3
% 1.92/1.01  --inst_sel_renew                        solver
% 1.92/1.01  --inst_lit_activity_flag                true
% 1.92/1.01  --inst_restr_to_given                   false
% 1.92/1.01  --inst_activity_threshold               500
% 1.92/1.01  --inst_out_proof                        true
% 1.92/1.01  
% 1.92/1.01  ------ Resolution Options
% 1.92/1.01  
% 1.92/1.01  --resolution_flag                       true
% 1.92/1.01  --res_lit_sel                           adaptive
% 1.92/1.01  --res_lit_sel_side                      none
% 1.92/1.01  --res_ordering                          kbo
% 1.92/1.01  --res_to_prop_solver                    active
% 1.92/1.01  --res_prop_simpl_new                    false
% 1.92/1.01  --res_prop_simpl_given                  true
% 1.92/1.01  --res_passive_queue_type                priority_queues
% 1.92/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.01  --res_passive_queues_freq               [15;5]
% 1.92/1.01  --res_forward_subs                      full
% 1.92/1.01  --res_backward_subs                     full
% 1.92/1.01  --res_forward_subs_resolution           true
% 1.92/1.01  --res_backward_subs_resolution          true
% 1.92/1.01  --res_orphan_elimination                true
% 1.92/1.01  --res_time_limit                        2.
% 1.92/1.01  --res_out_proof                         true
% 1.92/1.01  
% 1.92/1.01  ------ Superposition Options
% 1.92/1.01  
% 1.92/1.01  --superposition_flag                    true
% 1.92/1.01  --sup_passive_queue_type                priority_queues
% 1.92/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.01  --demod_completeness_check              fast
% 1.92/1.01  --demod_use_ground                      true
% 1.92/1.01  --sup_to_prop_solver                    passive
% 1.92/1.01  --sup_prop_simpl_new                    true
% 1.92/1.01  --sup_prop_simpl_given                  true
% 1.92/1.01  --sup_fun_splitting                     false
% 1.92/1.01  --sup_smt_interval                      50000
% 1.92/1.01  
% 1.92/1.01  ------ Superposition Simplification Setup
% 1.92/1.01  
% 1.92/1.01  --sup_indices_passive                   []
% 1.92/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_full_bw                           [BwDemod]
% 1.92/1.01  --sup_immed_triv                        [TrivRules]
% 1.92/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_immed_bw_main                     []
% 1.92/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.01  
% 1.92/1.01  ------ Combination Options
% 1.92/1.01  
% 1.92/1.01  --comb_res_mult                         3
% 1.92/1.01  --comb_sup_mult                         2
% 1.92/1.01  --comb_inst_mult                        10
% 1.92/1.01  
% 1.92/1.01  ------ Debug Options
% 1.92/1.01  
% 1.92/1.01  --dbg_backtrace                         false
% 1.92/1.01  --dbg_dump_prop_clauses                 false
% 1.92/1.01  --dbg_dump_prop_clauses_file            -
% 1.92/1.01  --dbg_out_stat                          false
% 1.92/1.01  ------ Parsing...
% 1.92/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.92/1.01  ------ Proving...
% 1.92/1.01  ------ Problem Properties 
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  clauses                                 37
% 1.92/1.01  conjectures                             6
% 1.92/1.01  EPR                                     8
% 1.92/1.01  Horn                                    12
% 1.92/1.01  unary                                   6
% 1.92/1.01  binary                                  4
% 1.92/1.01  lits                                    181
% 1.92/1.01  lits eq                                 17
% 1.92/1.01  fd_pure                                 0
% 1.92/1.01  fd_pseudo                               0
% 1.92/1.01  fd_cond                                 0
% 1.92/1.01  fd_pseudo_cond                          7
% 1.92/1.01  AC symbols                              0
% 1.92/1.01  
% 1.92/1.01  ------ Schedule dynamic 5 is on 
% 1.92/1.01  
% 1.92/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  ------ 
% 1.92/1.01  Current options:
% 1.92/1.01  ------ 
% 1.92/1.01  
% 1.92/1.01  ------ Input Options
% 1.92/1.01  
% 1.92/1.01  --out_options                           all
% 1.92/1.01  --tptp_safe_out                         true
% 1.92/1.01  --problem_path                          ""
% 1.92/1.01  --include_path                          ""
% 1.92/1.01  --clausifier                            res/vclausify_rel
% 1.92/1.01  --clausifier_options                    --mode clausify
% 1.92/1.01  --stdin                                 false
% 1.92/1.01  --stats_out                             all
% 1.92/1.01  
% 1.92/1.01  ------ General Options
% 1.92/1.01  
% 1.92/1.01  --fof                                   false
% 1.92/1.01  --time_out_real                         305.
% 1.92/1.01  --time_out_virtual                      -1.
% 1.92/1.01  --symbol_type_check                     false
% 1.92/1.01  --clausify_out                          false
% 1.92/1.01  --sig_cnt_out                           false
% 1.92/1.01  --trig_cnt_out                          false
% 1.92/1.01  --trig_cnt_out_tolerance                1.
% 1.92/1.01  --trig_cnt_out_sk_spl                   false
% 1.92/1.01  --abstr_cl_out                          false
% 1.92/1.01  
% 1.92/1.01  ------ Global Options
% 1.92/1.01  
% 1.92/1.01  --schedule                              default
% 1.92/1.01  --add_important_lit                     false
% 1.92/1.01  --prop_solver_per_cl                    1000
% 1.92/1.01  --min_unsat_core                        false
% 1.92/1.01  --soft_assumptions                      false
% 1.92/1.01  --soft_lemma_size                       3
% 1.92/1.01  --prop_impl_unit_size                   0
% 1.92/1.01  --prop_impl_unit                        []
% 1.92/1.01  --share_sel_clauses                     true
% 1.92/1.01  --reset_solvers                         false
% 1.92/1.01  --bc_imp_inh                            [conj_cone]
% 1.92/1.01  --conj_cone_tolerance                   3.
% 1.92/1.01  --extra_neg_conj                        none
% 1.92/1.01  --large_theory_mode                     true
% 1.92/1.01  --prolific_symb_bound                   200
% 1.92/1.01  --lt_threshold                          2000
% 1.92/1.01  --clause_weak_htbl                      true
% 1.92/1.01  --gc_record_bc_elim                     false
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing Options
% 1.92/1.01  
% 1.92/1.01  --preprocessing_flag                    true
% 1.92/1.01  --time_out_prep_mult                    0.1
% 1.92/1.01  --splitting_mode                        input
% 1.92/1.01  --splitting_grd                         true
% 1.92/1.01  --splitting_cvd                         false
% 1.92/1.01  --splitting_cvd_svl                     false
% 1.92/1.01  --splitting_nvd                         32
% 1.92/1.01  --sub_typing                            true
% 1.92/1.01  --prep_gs_sim                           true
% 1.92/1.01  --prep_unflatten                        true
% 1.92/1.01  --prep_res_sim                          true
% 1.92/1.01  --prep_upred                            true
% 1.92/1.01  --prep_sem_filter                       exhaustive
% 1.92/1.01  --prep_sem_filter_out                   false
% 1.92/1.01  --pred_elim                             true
% 1.92/1.01  --res_sim_input                         true
% 1.92/1.01  --eq_ax_congr_red                       true
% 1.92/1.01  --pure_diseq_elim                       true
% 1.92/1.01  --brand_transform                       false
% 1.92/1.01  --non_eq_to_eq                          false
% 1.92/1.01  --prep_def_merge                        true
% 1.92/1.01  --prep_def_merge_prop_impl              false
% 1.92/1.01  --prep_def_merge_mbd                    true
% 1.92/1.01  --prep_def_merge_tr_red                 false
% 1.92/1.01  --prep_def_merge_tr_cl                  false
% 1.92/1.01  --smt_preprocessing                     true
% 1.92/1.01  --smt_ac_axioms                         fast
% 1.92/1.01  --preprocessed_out                      false
% 1.92/1.01  --preprocessed_stats                    false
% 1.92/1.01  
% 1.92/1.01  ------ Abstraction refinement Options
% 1.92/1.01  
% 1.92/1.01  --abstr_ref                             []
% 1.92/1.01  --abstr_ref_prep                        false
% 1.92/1.01  --abstr_ref_until_sat                   false
% 1.92/1.01  --abstr_ref_sig_restrict                funpre
% 1.92/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/1.01  --abstr_ref_under                       []
% 1.92/1.01  
% 1.92/1.01  ------ SAT Options
% 1.92/1.01  
% 1.92/1.01  --sat_mode                              false
% 1.92/1.01  --sat_fm_restart_options                ""
% 1.92/1.01  --sat_gr_def                            false
% 1.92/1.01  --sat_epr_types                         true
% 1.92/1.01  --sat_non_cyclic_types                  false
% 1.92/1.01  --sat_finite_models                     false
% 1.92/1.01  --sat_fm_lemmas                         false
% 1.92/1.01  --sat_fm_prep                           false
% 1.92/1.01  --sat_fm_uc_incr                        true
% 1.92/1.01  --sat_out_model                         small
% 1.92/1.01  --sat_out_clauses                       false
% 1.92/1.01  
% 1.92/1.01  ------ QBF Options
% 1.92/1.01  
% 1.92/1.01  --qbf_mode                              false
% 1.92/1.01  --qbf_elim_univ                         false
% 1.92/1.01  --qbf_dom_inst                          none
% 1.92/1.01  --qbf_dom_pre_inst                      false
% 1.92/1.01  --qbf_sk_in                             false
% 1.92/1.01  --qbf_pred_elim                         true
% 1.92/1.01  --qbf_split                             512
% 1.92/1.01  
% 1.92/1.01  ------ BMC1 Options
% 1.92/1.01  
% 1.92/1.01  --bmc1_incremental                      false
% 1.92/1.01  --bmc1_axioms                           reachable_all
% 1.92/1.01  --bmc1_min_bound                        0
% 1.92/1.01  --bmc1_max_bound                        -1
% 1.92/1.01  --bmc1_max_bound_default                -1
% 1.92/1.01  --bmc1_symbol_reachability              true
% 1.92/1.01  --bmc1_property_lemmas                  false
% 1.92/1.01  --bmc1_k_induction                      false
% 1.92/1.01  --bmc1_non_equiv_states                 false
% 1.92/1.01  --bmc1_deadlock                         false
% 1.92/1.01  --bmc1_ucm                              false
% 1.92/1.01  --bmc1_add_unsat_core                   none
% 1.92/1.01  --bmc1_unsat_core_children              false
% 1.92/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/1.01  --bmc1_out_stat                         full
% 1.92/1.01  --bmc1_ground_init                      false
% 1.92/1.01  --bmc1_pre_inst_next_state              false
% 1.92/1.01  --bmc1_pre_inst_state                   false
% 1.92/1.01  --bmc1_pre_inst_reach_state             false
% 1.92/1.01  --bmc1_out_unsat_core                   false
% 1.92/1.01  --bmc1_aig_witness_out                  false
% 1.92/1.01  --bmc1_verbose                          false
% 1.92/1.01  --bmc1_dump_clauses_tptp                false
% 1.92/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.92/1.01  --bmc1_dump_file                        -
% 1.92/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.92/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.92/1.01  --bmc1_ucm_extend_mode                  1
% 1.92/1.01  --bmc1_ucm_init_mode                    2
% 1.92/1.01  --bmc1_ucm_cone_mode                    none
% 1.92/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.92/1.01  --bmc1_ucm_relax_model                  4
% 1.92/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.92/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/1.01  --bmc1_ucm_layered_model                none
% 1.92/1.01  --bmc1_ucm_max_lemma_size               10
% 1.92/1.01  
% 1.92/1.01  ------ AIG Options
% 1.92/1.01  
% 1.92/1.01  --aig_mode                              false
% 1.92/1.01  
% 1.92/1.01  ------ Instantiation Options
% 1.92/1.01  
% 1.92/1.01  --instantiation_flag                    true
% 1.92/1.01  --inst_sos_flag                         false
% 1.92/1.01  --inst_sos_phase                        true
% 1.92/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/1.01  --inst_lit_sel_side                     none
% 1.92/1.01  --inst_solver_per_active                1400
% 1.92/1.01  --inst_solver_calls_frac                1.
% 1.92/1.01  --inst_passive_queue_type               priority_queues
% 1.92/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/1.01  --inst_passive_queues_freq              [25;2]
% 1.92/1.01  --inst_dismatching                      true
% 1.92/1.01  --inst_eager_unprocessed_to_passive     true
% 1.92/1.01  --inst_prop_sim_given                   true
% 1.92/1.01  --inst_prop_sim_new                     false
% 1.92/1.01  --inst_subs_new                         false
% 1.92/1.01  --inst_eq_res_simp                      false
% 1.92/1.01  --inst_subs_given                       false
% 1.92/1.01  --inst_orphan_elimination               true
% 1.92/1.01  --inst_learning_loop_flag               true
% 1.92/1.01  --inst_learning_start                   3000
% 1.92/1.01  --inst_learning_factor                  2
% 1.92/1.01  --inst_start_prop_sim_after_learn       3
% 1.92/1.01  --inst_sel_renew                        solver
% 1.92/1.01  --inst_lit_activity_flag                true
% 1.92/1.01  --inst_restr_to_given                   false
% 1.92/1.01  --inst_activity_threshold               500
% 1.92/1.01  --inst_out_proof                        true
% 1.92/1.01  
% 1.92/1.01  ------ Resolution Options
% 1.92/1.01  
% 1.92/1.01  --resolution_flag                       false
% 1.92/1.01  --res_lit_sel                           adaptive
% 1.92/1.01  --res_lit_sel_side                      none
% 1.92/1.01  --res_ordering                          kbo
% 1.92/1.01  --res_to_prop_solver                    active
% 1.92/1.01  --res_prop_simpl_new                    false
% 1.92/1.01  --res_prop_simpl_given                  true
% 1.92/1.01  --res_passive_queue_type                priority_queues
% 1.92/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.01  --res_passive_queues_freq               [15;5]
% 1.92/1.01  --res_forward_subs                      full
% 1.92/1.01  --res_backward_subs                     full
% 1.92/1.01  --res_forward_subs_resolution           true
% 1.92/1.01  --res_backward_subs_resolution          true
% 1.92/1.01  --res_orphan_elimination                true
% 1.92/1.01  --res_time_limit                        2.
% 1.92/1.01  --res_out_proof                         true
% 1.92/1.01  
% 1.92/1.01  ------ Superposition Options
% 1.92/1.01  
% 1.92/1.01  --superposition_flag                    true
% 1.92/1.01  --sup_passive_queue_type                priority_queues
% 1.92/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.01  --demod_completeness_check              fast
% 1.92/1.01  --demod_use_ground                      true
% 1.92/1.01  --sup_to_prop_solver                    passive
% 1.92/1.01  --sup_prop_simpl_new                    true
% 1.92/1.01  --sup_prop_simpl_given                  true
% 1.92/1.01  --sup_fun_splitting                     false
% 1.92/1.01  --sup_smt_interval                      50000
% 1.92/1.01  
% 1.92/1.01  ------ Superposition Simplification Setup
% 1.92/1.01  
% 1.92/1.01  --sup_indices_passive                   []
% 1.92/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_full_bw                           [BwDemod]
% 1.92/1.01  --sup_immed_triv                        [TrivRules]
% 1.92/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_immed_bw_main                     []
% 1.92/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.01  
% 1.92/1.01  ------ Combination Options
% 1.92/1.01  
% 1.92/1.01  --comb_res_mult                         3
% 1.92/1.01  --comb_sup_mult                         2
% 1.92/1.01  --comb_inst_mult                        10
% 1.92/1.01  
% 1.92/1.01  ------ Debug Options
% 1.92/1.01  
% 1.92/1.01  --dbg_backtrace                         false
% 1.92/1.01  --dbg_dump_prop_clauses                 false
% 1.92/1.01  --dbg_dump_prop_clauses_file            -
% 1.92/1.01  --dbg_out_stat                          false
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  ------ Proving...
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  % SZS status Theorem for theBenchmark.p
% 1.92/1.01  
% 1.92/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.92/1.01  
% 1.92/1.01  fof(f17,conjecture,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f18,negated_conjecture,(
% 1.92/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.92/1.01    inference(negated_conjecture,[],[f17])).
% 1.92/1.01  
% 1.92/1.01  fof(f44,plain,(
% 1.92/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f18])).
% 1.92/1.01  
% 1.92/1.01  fof(f45,plain,(
% 1.92/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f44])).
% 1.92/1.01  
% 1.92/1.01  fof(f64,plain,(
% 1.92/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK6) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f63,plain,(
% 1.92/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK5,k8_tmap_1(X0,sK5),k2_tmap_1(X0,k8_tmap_1(X0,sK5),k9_tmap_1(X0,sK5),sK5),X2) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f62,plain,(
% 1.92/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK4,X1),k2_tmap_1(sK4,k8_tmap_1(sK4,X1),k9_tmap_1(sK4,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK4) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f65,plain,(
% 1.92/1.01    ((~r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6) & m1_subset_1(sK6,u1_struct_0(sK5))) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f45,f64,f63,f62])).
% 1.92/1.01  
% 1.92/1.01  fof(f104,plain,(
% 1.92/1.01    m1_pre_topc(sK5,sK4)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f7,axiom,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f26,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f7])).
% 1.92/1.01  
% 1.92/1.01  fof(f27,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f26])).
% 1.92/1.01  
% 1.92/1.01  fof(f53,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(nnf_transformation,[],[f27])).
% 1.92/1.01  
% 1.92/1.01  fof(f54,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(rectify,[],[f53])).
% 1.92/1.01  
% 1.92/1.01  fof(f55,plain,(
% 1.92/1.01    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f56,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 1.92/1.01  
% 1.92/1.01  fof(f76,plain,(
% 1.92/1.01    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f56])).
% 1.92/1.01  
% 1.92/1.01  fof(f108,plain,(
% 1.92/1.01    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(equality_resolution,[],[f76])).
% 1.92/1.01  
% 1.92/1.01  fof(f109,plain,(
% 1.92/1.01    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(equality_resolution,[],[f108])).
% 1.92/1.01  
% 1.92/1.01  fof(f16,axiom,(
% 1.92/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f43,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.92/1.01    inference(ennf_transformation,[],[f16])).
% 1.92/1.01  
% 1.92/1.01  fof(f99,plain,(
% 1.92/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f43])).
% 1.92/1.01  
% 1.92/1.01  fof(f11,axiom,(
% 1.92/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f33,plain,(
% 1.92/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f11])).
% 1.92/1.01  
% 1.92/1.01  fof(f34,plain,(
% 1.92/1.01    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f33])).
% 1.92/1.01  
% 1.92/1.01  fof(f89,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f34])).
% 1.92/1.01  
% 1.92/1.01  fof(f90,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f34])).
% 1.92/1.01  
% 1.92/1.01  fof(f91,plain,(
% 1.92/1.01    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f34])).
% 1.92/1.01  
% 1.92/1.01  fof(f100,plain,(
% 1.92/1.01    ~v2_struct_0(sK4)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f101,plain,(
% 1.92/1.01    v2_pre_topc(sK4)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f102,plain,(
% 1.92/1.01    l1_pre_topc(sK4)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f8,axiom,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f28,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f8])).
% 1.92/1.01  
% 1.92/1.01  fof(f29,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f28])).
% 1.92/1.01  
% 1.92/1.01  fof(f57,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(nnf_transformation,[],[f29])).
% 1.92/1.01  
% 1.92/1.01  fof(f58,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(rectify,[],[f57])).
% 1.92/1.01  
% 1.92/1.01  fof(f59,plain,(
% 1.92/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f60,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 1.92/1.01  
% 1.92/1.01  fof(f80,plain,(
% 1.92/1.01    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f60])).
% 1.92/1.01  
% 1.92/1.01  fof(f110,plain,(
% 1.92/1.01    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(equality_resolution,[],[f80])).
% 1.92/1.01  
% 1.92/1.01  fof(f111,plain,(
% 1.92/1.01    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(equality_resolution,[],[f110])).
% 1.92/1.01  
% 1.92/1.01  fof(f12,axiom,(
% 1.92/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f35,plain,(
% 1.92/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f12])).
% 1.92/1.01  
% 1.92/1.01  fof(f36,plain,(
% 1.92/1.01    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f35])).
% 1.92/1.01  
% 1.92/1.01  fof(f93,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f36])).
% 1.92/1.01  
% 1.92/1.01  fof(f92,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f36])).
% 1.92/1.01  
% 1.92/1.01  fof(f94,plain,(
% 1.92/1.01    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f36])).
% 1.92/1.01  
% 1.92/1.01  fof(f13,axiom,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f37,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f13])).
% 1.92/1.01  
% 1.92/1.01  fof(f38,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f37])).
% 1.92/1.01  
% 1.92/1.01  fof(f95,plain,(
% 1.92/1.01    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f38])).
% 1.92/1.01  
% 1.92/1.01  fof(f6,axiom,(
% 1.92/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f24,plain,(
% 1.92/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.92/1.01    inference(ennf_transformation,[],[f6])).
% 1.92/1.01  
% 1.92/1.01  fof(f25,plain,(
% 1.92/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.92/1.01    inference(flattening,[],[f24])).
% 1.92/1.01  
% 1.92/1.01  fof(f52,plain,(
% 1.92/1.01    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.92/1.01    inference(nnf_transformation,[],[f25])).
% 1.92/1.01  
% 1.92/1.01  fof(f74,plain,(
% 1.92/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f52])).
% 1.92/1.01  
% 1.92/1.01  fof(f10,axiom,(
% 1.92/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f31,plain,(
% 1.92/1.01    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f10])).
% 1.92/1.01  
% 1.92/1.01  fof(f32,plain,(
% 1.92/1.01    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f31])).
% 1.92/1.01  
% 1.92/1.01  fof(f88,plain,(
% 1.92/1.01    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f32])).
% 1.92/1.01  
% 1.92/1.01  fof(f87,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f32])).
% 1.92/1.01  
% 1.92/1.01  fof(f1,axiom,(
% 1.92/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f46,plain,(
% 1.92/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.92/1.01    inference(nnf_transformation,[],[f1])).
% 1.92/1.01  
% 1.92/1.01  fof(f47,plain,(
% 1.92/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.92/1.01    inference(rectify,[],[f46])).
% 1.92/1.01  
% 1.92/1.01  fof(f48,plain,(
% 1.92/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f49,plain,(
% 1.92/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 1.92/1.01  
% 1.92/1.01  fof(f67,plain,(
% 1.92/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f49])).
% 1.92/1.01  
% 1.92/1.01  fof(f3,axiom,(
% 1.92/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f21,plain,(
% 1.92/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.92/1.01    inference(ennf_transformation,[],[f3])).
% 1.92/1.01  
% 1.92/1.01  fof(f71,plain,(
% 1.92/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f21])).
% 1.92/1.01  
% 1.92/1.01  fof(f2,axiom,(
% 1.92/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f19,plain,(
% 1.92/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/1.01    inference(rectify,[],[f2])).
% 1.92/1.01  
% 1.92/1.01  fof(f20,plain,(
% 1.92/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.92/1.01    inference(ennf_transformation,[],[f19])).
% 1.92/1.01  
% 1.92/1.01  fof(f50,plain,(
% 1.92/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.92/1.01    introduced(choice_axiom,[])).
% 1.92/1.01  
% 1.92/1.01  fof(f51,plain,(
% 1.92/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f50])).
% 1.92/1.01  
% 1.92/1.01  fof(f69,plain,(
% 1.92/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f51])).
% 1.92/1.01  
% 1.92/1.01  fof(f66,plain,(
% 1.92/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f49])).
% 1.92/1.01  
% 1.92/1.01  fof(f4,axiom,(
% 1.92/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f22,plain,(
% 1.92/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.92/1.01    inference(ennf_transformation,[],[f4])).
% 1.92/1.01  
% 1.92/1.01  fof(f72,plain,(
% 1.92/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f22])).
% 1.92/1.01  
% 1.92/1.01  fof(f9,axiom,(
% 1.92/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f30,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.92/1.01    inference(ennf_transformation,[],[f9])).
% 1.92/1.01  
% 1.92/1.01  fof(f61,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.92/1.01    inference(nnf_transformation,[],[f30])).
% 1.92/1.01  
% 1.92/1.01  fof(f85,plain,(
% 1.92/1.01    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f61])).
% 1.92/1.01  
% 1.92/1.01  fof(f15,axiom,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f41,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f15])).
% 1.92/1.01  
% 1.92/1.01  fof(f42,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f41])).
% 1.92/1.01  
% 1.92/1.01  fof(f98,plain,(
% 1.92/1.01    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f42])).
% 1.92/1.01  
% 1.92/1.01  fof(f106,plain,(
% 1.92/1.01    ~r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f103,plain,(
% 1.92/1.01    ~v2_struct_0(sK5)),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f105,plain,(
% 1.92/1.01    m1_subset_1(sK6,u1_struct_0(sK5))),
% 1.92/1.01    inference(cnf_transformation,[],[f65])).
% 1.92/1.01  
% 1.92/1.01  fof(f5,axiom,(
% 1.92/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f23,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.92/1.01    inference(ennf_transformation,[],[f5])).
% 1.92/1.01  
% 1.92/1.01  fof(f73,plain,(
% 1.92/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f23])).
% 1.92/1.01  
% 1.92/1.01  fof(f86,plain,(
% 1.92/1.01    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f32])).
% 1.92/1.01  
% 1.92/1.01  fof(f14,axiom,(
% 1.92/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.92/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/1.01  
% 1.92/1.01  fof(f39,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/1.01    inference(ennf_transformation,[],[f14])).
% 1.92/1.01  
% 1.92/1.01  fof(f40,plain,(
% 1.92/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/1.01    inference(flattening,[],[f39])).
% 1.92/1.01  
% 1.92/1.01  fof(f97,plain,(
% 1.92/1.01    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(cnf_transformation,[],[f40])).
% 1.92/1.01  
% 1.92/1.01  fof(f112,plain,(
% 1.92/1.01    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/1.01    inference(equality_resolution,[],[f97])).
% 1.92/1.01  
% 1.92/1.01  cnf(c_36,negated_conjecture,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) ),
% 1.92/1.01      inference(cnf_transformation,[],[f104]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1767,negated_conjecture,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_36]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2579,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_13,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 1.92/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f109]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_33,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f99]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_25,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v1_pre_topc(k8_tmap_1(X1,X0))
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f89]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_24,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | v2_pre_topc(k8_tmap_1(X1,X0))
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f90]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_23,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 1.92/1.01      inference(cnf_transformation,[],[f91]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_268,plain,
% 1.92/1.01      ( ~ l1_pre_topc(X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_13,c_33,c_25,c_24,c_23]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_269,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.92/1.01      inference(renaming,[status(thm)],[c_268]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1761,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0_60,X1_60)
% 1.92/1.01      | v2_struct_0(X1_60)
% 1.92/1.01      | ~ v2_pre_topc(X1_60)
% 1.92/1.01      | ~ l1_pre_topc(X1_60)
% 1.92/1.01      | k6_tmap_1(X1_60,u1_struct_0(X0_60)) = k8_tmap_1(X1_60,X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_269]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2585,plain,
% 1.92/1.01      ( k6_tmap_1(X0_60,u1_struct_0(X1_60)) = k8_tmap_1(X0_60,X1_60)
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4353,plain,
% 1.92/1.01      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5)
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2579,c_2585]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_40,negated_conjecture,
% 1.92/1.01      ( ~ v2_struct_0(sK4) ),
% 1.92/1.01      inference(cnf_transformation,[],[f100]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_39,negated_conjecture,
% 1.92/1.01      ( v2_pre_topc(sK4) ),
% 1.92/1.01      inference(cnf_transformation,[],[f101]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_38,negated_conjecture,
% 1.92/1.01      ( l1_pre_topc(sK4) ),
% 1.92/1.01      inference(cnf_transformation,[],[f102]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3067,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,sK4)
% 1.92/1.01      | v2_struct_0(sK4)
% 1.92/1.01      | ~ v2_pre_topc(sK4)
% 1.92/1.01      | ~ l1_pre_topc(sK4)
% 1.92/1.01      | k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1761]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4356,plain,
% 1.92/1.01      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_4353,c_40,c_39,c_38,c_36,c_3067]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_17,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 1.92/1.01      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.92/1.01      | ~ m1_pre_topc(X1,X0)
% 1.92/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.92/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.92/1.01      | ~ l1_pre_topc(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f111]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_27,plain,
% 1.92/1.01      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.92/1.01      | ~ m1_pre_topc(X1,X0)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ l1_pre_topc(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f93]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_258,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 1.92/1.01      | ~ m1_pre_topc(X1,X0)
% 1.92/1.01      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.92/1.01      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.92/1.01      | ~ l1_pre_topc(X0) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_17,c_27]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1762,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60)))
% 1.92/1.01      | ~ m1_pre_topc(X1_60,X0_60)
% 1.92/1.01      | ~ m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))))
% 1.92/1.01      | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60)))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ v1_funct_1(k9_tmap_1(X0_60,X1_60))
% 1.92/1.01      | ~ l1_pre_topc(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_258]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2584,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))))) != iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | v1_funct_1(k9_tmap_1(X0_60,X1_60)) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_28,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | v1_funct_1(k9_tmap_1(X1,X0))
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f92]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1772,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0_60,X1_60)
% 1.92/1.01      | v2_struct_0(X1_60)
% 1.92/1.01      | ~ v2_pre_topc(X1_60)
% 1.92/1.01      | v1_funct_1(k9_tmap_1(X1_60,X0_60))
% 1.92/1.01      | ~ l1_pre_topc(X1_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2574,plain,
% 1.92/1.01      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 1.92/1.01      | v2_struct_0(X1_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X1_60) != iProver_top
% 1.92/1.01      | v1_funct_1(k9_tmap_1(X1_60,X0_60)) = iProver_top
% 1.92/1.01      | l1_pre_topc(X1_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1769,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0_60,X1_60)
% 1.92/1.01      | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60)))
% 1.92/1.01      | ~ l1_pre_topc(X1_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_33]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2577,plain,
% 1.92/1.01      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60))) = iProver_top
% 1.92/1.01      | l1_pre_topc(X1_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_26,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f94]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1774,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0_60,X1_60)
% 1.92/1.01      | m1_subset_1(k9_tmap_1(X1_60,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_60),u1_struct_0(k8_tmap_1(X1_60,X0_60)))))
% 1.92/1.01      | v2_struct_0(X1_60)
% 1.92/1.01      | ~ v2_pre_topc(X1_60)
% 1.92/1.01      | ~ l1_pre_topc(X1_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_26]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2572,plain,
% 1.92/1.01      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 1.92/1.01      | m1_subset_1(k9_tmap_1(X1_60,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_60),u1_struct_0(k8_tmap_1(X1_60,X0_60))))) = iProver_top
% 1.92/1.01      | v2_struct_0(X1_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X1_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X1_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2924,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(forward_subsumption_resolution,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_2584,c_2574,c_2577,c_2572]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_6603,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
% 1.92/1.01      | m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_4356,c_2924]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_30,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f95]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1770,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ l1_pre_topc(X0_60)
% 1.92/1.01      | u1_struct_0(k6_tmap_1(X0_60,X0_61)) = u1_struct_0(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2576,plain,
% 1.92/1.01      ( u1_struct_0(k6_tmap_1(X0_60,X0_61)) = u1_struct_0(X0_60)
% 1.92/1.01      | m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1770]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4183,plain,
% 1.92/1.01      ( u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))) = u1_struct_0(X0_60)
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2577,c_2576]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4543,plain,
% 1.92/1.01      ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4)
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2579,c_4183]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4544,plain,
% 1.92/1.01      ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4)
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(light_normalisation,[status(thm)],[c_4543,c_4356]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_41,plain,
% 1.92/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_42,plain,
% 1.92/1.01      ( v2_pre_topc(sK4) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_43,plain,
% 1.92/1.01      ( l1_pre_topc(sK4) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4547,plain,
% 1.92/1.01      ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_4544,c_41,c_42,c_43]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_6648,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
% 1.92/1.01      | m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(light_normalisation,[status(thm)],[c_6603,c_4547]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_45,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_6887,plain,
% 1.92/1.01      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK4),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_6648,c_41,c_42,c_43,c_45]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_9,plain,
% 1.92/1.01      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.92/1.01      | ~ v1_funct_2(X5,X2,X3)
% 1.92/1.01      | ~ v1_funct_2(X4,X0,X1)
% 1.92/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.92/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.92/1.01      | ~ v1_funct_1(X5)
% 1.92/1.01      | ~ v1_funct_1(X4)
% 1.92/1.01      | v1_xboole_0(X1)
% 1.92/1.01      | v1_xboole_0(X3)
% 1.92/1.01      | X4 = X5 ),
% 1.92/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1787,plain,
% 1.92/1.01      ( ~ r1_funct_2(X0_61,X1_61,X2_61,X3_61,X4_61,X5_61)
% 1.92/1.01      | ~ v1_funct_2(X5_61,X2_61,X3_61)
% 1.92/1.01      | ~ v1_funct_2(X4_61,X0_61,X1_61)
% 1.92/1.01      | ~ m1_subset_1(X5_61,k1_zfmisc_1(k2_zfmisc_1(X2_61,X3_61)))
% 1.92/1.01      | ~ m1_subset_1(X4_61,k1_zfmisc_1(k2_zfmisc_1(X0_61,X1_61)))
% 1.92/1.01      | ~ v1_funct_1(X5_61)
% 1.92/1.01      | ~ v1_funct_1(X4_61)
% 1.92/1.01      | v1_xboole_0(X1_61)
% 1.92/1.01      | v1_xboole_0(X3_61)
% 1.92/1.01      | X4_61 = X5_61 ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2559,plain,
% 1.92/1.01      ( X0_61 = X1_61
% 1.92/1.01      | r1_funct_2(X2_61,X3_61,X4_61,X5_61,X0_61,X1_61) != iProver_top
% 1.92/1.01      | v1_funct_2(X0_61,X2_61,X3_61) != iProver_top
% 1.92/1.01      | v1_funct_2(X1_61,X4_61,X5_61) != iProver_top
% 1.92/1.01      | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(X2_61,X3_61))) != iProver_top
% 1.92/1.01      | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(X4_61,X5_61))) != iProver_top
% 1.92/1.01      | v1_funct_1(X0_61) != iProver_top
% 1.92/1.01      | v1_funct_1(X1_61) != iProver_top
% 1.92/1.01      | v1_xboole_0(X5_61) = iProver_top
% 1.92/1.01      | v1_xboole_0(X3_61) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_6892,plain,
% 1.92/1.01      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 1.92/1.01      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 1.92/1.01      | v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 1.92/1.01      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 1.92/1.01      | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 1.92/1.01      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 1.92/1.01      | v1_funct_1(k9_tmap_1(sK4,sK5)) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_6887,c_2559]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_20,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f88]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1780,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
% 1.92/1.01      | m1_subset_1(k7_tmap_1(X0_60,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61)))))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ l1_pre_topc(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2566,plain,
% 1.92/1.01      ( m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 1.92/1.01      | m1_subset_1(k7_tmap_1(X0_60,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61))))) = iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_5059,plain,
% 1.92/1.01      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_4356,c_2566]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_5078,plain,
% 1.92/1.01      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(light_normalisation,[status(thm)],[c_5059,c_4547]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4915,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_4547,c_2572]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1773,plain,
% 1.92/1.01      ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))
% 1.92/1.01      | ~ m1_pre_topc(X1_60,X0_60)
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ l1_pre_topc(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2573,plain,
% 1.92/1.01      ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))) = iProver_top
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1773]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4560,plain,
% 1.92/1.01      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
% 1.92/1.01      | m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_4547,c_2573]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_21,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 1.92/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ l1_pre_topc(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f87]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1779,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(X0_60,X0_61),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61)))
% 1.92/1.01      | ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ l1_pre_topc(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2567,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(X0_60,X0_61),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_61))) = iProver_top
% 1.92/1.01      | m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4360,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_4356,c_2567]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3038,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,sK4)
% 1.92/1.01      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.01      | ~ l1_pre_topc(sK4) ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1769]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3039,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_3038]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4467,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_4360,c_41,c_42,c_43,c_45,c_3039]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_4550,plain,
% 1.92/1.01      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 1.92/1.01      inference(demodulation,[status(thm)],[c_4547,c_4467]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_0,plain,
% 1.92/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1795,plain,
% 1.92/1.01      ( r2_hidden(sK0(X0_61),X0_61) | v1_xboole_0(X0_61) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2551,plain,
% 1.92/1.01      ( r2_hidden(sK0(X0_61),X0_61) = iProver_top
% 1.92/1.01      | v1_xboole_0(X0_61) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1795]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_5,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.92/1.01      | ~ r2_hidden(X2,X0)
% 1.92/1.01      | ~ v1_xboole_0(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1790,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0_61,k1_zfmisc_1(X1_61))
% 1.92/1.01      | ~ r2_hidden(X0_64,X0_61)
% 1.92/1.01      | ~ v1_xboole_0(X1_61) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2556,plain,
% 1.92/1.01      ( m1_subset_1(X0_61,k1_zfmisc_1(X1_61)) != iProver_top
% 1.92/1.01      | r2_hidden(X0_64,X0_61) != iProver_top
% 1.92/1.01      | v1_xboole_0(X1_61) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3551,plain,
% 1.92/1.01      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 1.92/1.01      | r2_hidden(X0_64,u1_struct_0(X0_60)) != iProver_top
% 1.92/1.01      | l1_pre_topc(X1_60) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(X1_60)) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2577,c_2556]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3713,plain,
% 1.92/1.01      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X1_60) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(X1_60)) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(X0_60)) = iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2551,c_3551]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3810,plain,
% 1.92/1.01      ( l1_pre_topc(sK4) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 1.92/1.01      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2579,c_3713]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3,plain,
% 1.92/1.01      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1792,plain,
% 1.92/1.01      ( r1_xboole_0(X0_61,X1_61) | r2_hidden(sK1(X0_61,X1_61),X1_61) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2554,plain,
% 1.92/1.01      ( r1_xboole_0(X0_61,X1_61) = iProver_top
% 1.92/1.01      | r2_hidden(sK1(X0_61,X1_61),X1_61) = iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1,plain,
% 1.92/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1794,plain,
% 1.92/1.01      ( ~ r2_hidden(X0_64,X0_61) | ~ v1_xboole_0(X0_61) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2552,plain,
% 1.92/1.01      ( r2_hidden(X0_64,X0_61) != iProver_top
% 1.92/1.01      | v1_xboole_0(X0_61) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3144,plain,
% 1.92/1.01      ( r1_xboole_0(X0_61,X1_61) = iProver_top
% 1.92/1.01      | v1_xboole_0(X1_61) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_2554,c_2552]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_6,plain,
% 1.92/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_18,plain,
% 1.92/1.01      ( r1_tsep_1(X0,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 1.92/1.01      | ~ l1_struct_0(X1)
% 1.92/1.01      | ~ l1_struct_0(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f85]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_32,plain,
% 1.92/1.01      ( r1_tmap_1(X0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0),X3)
% 1.92/1.01      | ~ r1_tsep_1(X2,X0)
% 1.92/1.01      | ~ m1_pre_topc(X2,X1)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X2)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f98]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_34,negated_conjecture,
% 1.92/1.01      ( ~ r1_tmap_1(sK5,k8_tmap_1(sK4,sK5),k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5),sK6) ),
% 1.92/1.01      inference(cnf_transformation,[],[f106]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_510,plain,
% 1.92/1.01      ( ~ r1_tsep_1(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(X1,X2)
% 1.92/1.01      | ~ m1_pre_topc(X0,X2)
% 1.92/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X2)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X2)
% 1.92/1.01      | ~ l1_pre_topc(X2)
% 1.92/1.01      | k2_tmap_1(X2,k8_tmap_1(X2,X0),k9_tmap_1(X2,X0),X1) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X2,X0) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK6 != X3
% 1.92/1.01      | sK5 != X1 ),
% 1.92/1.01      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_511,plain,
% 1.92/1.01      ( ~ r1_tsep_1(X0,sK5)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(sK5)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(unflattening,[status(thm)],[c_510]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_37,negated_conjecture,
% 1.92/1.01      ( ~ v2_struct_0(sK5) ),
% 1.92/1.01      inference(cnf_transformation,[],[f103]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_35,negated_conjecture,
% 1.92/1.01      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.92/1.01      inference(cnf_transformation,[],[f105]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_515,plain,
% 1.92/1.01      ( v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ r1_tsep_1(X0,sK5)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_511,c_37,c_35]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_516,plain,
% 1.92/1.01      ( ~ r1_tsep_1(X0,sK5)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(renaming,[status(thm)],[c_515]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_567,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ l1_struct_0(X2)
% 1.92/1.01      | ~ l1_struct_0(X3)
% 1.92/1.01      | X0 != X2
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK5 != X3 ),
% 1.92/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_516]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_568,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ l1_struct_0(X0)
% 1.92/1.01      | ~ l1_struct_0(sK5)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_7,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.92/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_572,plain,
% 1.92/1.01      ( ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ l1_struct_0(sK5)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_568,c_7,c_6]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_573,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ l1_struct_0(sK5)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(renaming,[status(thm)],[c_572]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_620,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X2)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK5 != X2 ),
% 1.92/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_573]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_621,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(sK5)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(unflattening,[status(thm)],[c_620]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_645,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k8_tmap_1(X1,X0),k9_tmap_1(X1,X0),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_621,c_7]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1759,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0_60,X1_60)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X1_60)
% 1.92/1.01      | ~ r1_xboole_0(u1_struct_0(X0_60),u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | v2_struct_0(X1_60)
% 1.92/1.01      | ~ v2_pre_topc(X1_60)
% 1.92/1.01      | ~ l1_pre_topc(X1_60)
% 1.92/1.01      | k2_tmap_1(X1_60,k8_tmap_1(X1_60,X0_60),k9_tmap_1(X1_60,X0_60),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X1_60,X0_60) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_645]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_2587,plain,
% 1.92/1.01      ( k2_tmap_1(X0_60,k8_tmap_1(X0_60,X1_60),k9_tmap_1(X0_60,X1_60),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k8_tmap_1(X0_60,X1_60) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 1.92/1.01      | m1_pre_topc(sK5,X0_60) != iProver_top
% 1.92/1.01      | r1_xboole_0(u1_struct_0(X1_60),u1_struct_0(sK5)) != iProver_top
% 1.92/1.01      | v2_struct_0(X0_60) = iProver_top
% 1.92/1.01      | v2_struct_0(X1_60) = iProver_top
% 1.92/1.01      | v2_pre_topc(X0_60) != iProver_top
% 1.92/1.01      | l1_pre_topc(X0_60) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3100,plain,
% 1.92/1.01      ( k8_tmap_1(sK4,sK5) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_struct_0(sK5) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(equality_resolution,[status(thm)],[c_2587]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3220,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_struct_0(sK5) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(equality_resolution_simp,[status(thm)],[c_3100]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_44,plain,
% 1.92/1.01      ( v2_struct_0(sK5) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3222,plain,
% 1.92/1.01      ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_3220,c_41,c_42,c_43,c_44,c_45]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3271,plain,
% 1.92/1.01      ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 1.92/1.01      inference(superposition,[status(thm)],[c_3144,c_3222]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1825,plain,
% 1.92/1.01      ( k2_tmap_1(X0_60,X1_60,X0_61,X2_60) = k2_tmap_1(X3_60,X4_60,X1_61,X5_60)
% 1.92/1.01      | X0_61 != X1_61
% 1.92/1.01      | X0_60 != X3_60
% 1.92/1.01      | X1_60 != X4_60
% 1.92/1.01      | X2_60 != X5_60 ),
% 1.92/1.01      theory(equality) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3263,plain,
% 1.92/1.01      ( k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK5)),k7_tmap_1(X0_60,u1_struct_0(sK5)),sK5) = k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k7_tmap_1(X0_60,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 1.92/1.01      | X0_60 != sK4
% 1.92/1.01      | k6_tmap_1(X0_60,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK5 != sK5 ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1825]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3264,plain,
% 1.92/1.01      ( k2_tmap_1(sK4,k6_tmap_1(sK4,u1_struct_0(sK5)),k7_tmap_1(sK4,u1_struct_0(sK5)),sK5) = k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 1.92/1.01      | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK4 != sK4
% 1.92/1.01      | sK5 != sK5 ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_3263]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1797,plain,( X0_60 = X0_60 ),theory(equality) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3256,plain,
% 1.92/1.01      ( sK5 = sK5 ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1797]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_22,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | v1_funct_1(k7_tmap_1(X1,X0))
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f86]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1778,plain,
% 1.92/1.01      ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_60)))
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | v1_funct_1(k7_tmap_1(X0_60,X0_61))
% 1.92/1.01      | ~ l1_pre_topc(X0_60) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3151,plain,
% 1.92/1.01      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.01      | v2_struct_0(sK4)
% 1.92/1.01      | ~ v2_pre_topc(sK4)
% 1.92/1.01      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
% 1.92/1.01      | ~ l1_pre_topc(sK4) ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1778]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3152,plain,
% 1.92/1.01      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_3151]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3041,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,sK4)
% 1.92/1.01      | v2_struct_0(sK4)
% 1.92/1.01      | ~ v2_pre_topc(sK4)
% 1.92/1.01      | v1_funct_1(k9_tmap_1(sK4,sK5))
% 1.92/1.01      | ~ l1_pre_topc(sK4) ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1772]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_3042,plain,
% 1.92/1.01      ( m1_pre_topc(sK5,sK4) != iProver_top
% 1.92/1.01      | v2_struct_0(sK4) = iProver_top
% 1.92/1.01      | v2_pre_topc(sK4) != iProver_top
% 1.92/1.01      | v1_funct_1(k9_tmap_1(sK4,sK5)) = iProver_top
% 1.92/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 1.92/1.01      inference(predicate_to_equality,[status(thm)],[c_3041]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_31,plain,
% 1.92/1.01      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(cnf_transformation,[],[f112]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_238,plain,
% 1.92/1.01      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_31,c_33]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_239,plain,
% 1.92/1.01      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 1.92/1.01      | ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1) ),
% 1.92/1.01      inference(renaming,[status(thm)],[c_238]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_480,plain,
% 1.92/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.92/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(X1)
% 1.92/1.01      | ~ v2_pre_topc(X1)
% 1.92/1.01      | ~ l1_pre_topc(X1)
% 1.92/1.01      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK4,sK5)
% 1.92/1.01      | sK6 != X2
% 1.92/1.01      | sK5 != X0 ),
% 1.92/1.01      inference(resolution_lifted,[status(thm)],[c_239,c_34]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_481,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,X0)
% 1.92/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | v2_struct_0(sK5)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ l1_pre_topc(X0)
% 1.92/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(unflattening,[status(thm)],[c_480]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_485,plain,
% 1.92/1.01      ( v2_struct_0(X0)
% 1.92/1.01      | ~ m1_pre_topc(sK5,X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ l1_pre_topc(X0)
% 1.92/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(global_propositional_subsumption,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_481,c_37,c_35]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_486,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,X0)
% 1.92/1.01      | v2_struct_0(X0)
% 1.92/1.01      | ~ v2_pre_topc(X0)
% 1.92/1.01      | ~ l1_pre_topc(X0)
% 1.92/1.01      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK5)),k7_tmap_1(X0,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(X0,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(renaming,[status(thm)],[c_485]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1760,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,X0_60)
% 1.92/1.01      | v2_struct_0(X0_60)
% 1.92/1.01      | ~ v2_pre_topc(X0_60)
% 1.92/1.01      | ~ l1_pre_topc(X0_60)
% 1.92/1.01      | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK5)),k7_tmap_1(X0_60,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(X0_60,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(subtyping,[status(esa)],[c_486]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1922,plain,
% 1.92/1.01      ( ~ m1_pre_topc(sK5,sK4)
% 1.92/1.01      | v2_struct_0(sK4)
% 1.92/1.01      | ~ v2_pre_topc(sK4)
% 1.92/1.01      | ~ l1_pre_topc(sK4)
% 1.92/1.01      | k2_tmap_1(sK4,k6_tmap_1(sK4,u1_struct_0(sK5)),k7_tmap_1(sK4,u1_struct_0(sK5)),sK5) != k2_tmap_1(sK4,k8_tmap_1(sK4,sK5),k9_tmap_1(sK4,sK5),sK5)
% 1.92/1.01      | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5) ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1760]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(c_1847,plain,
% 1.92/1.01      ( sK4 = sK4 ),
% 1.92/1.01      inference(instantiation,[status(thm)],[c_1797]) ).
% 1.92/1.01  
% 1.92/1.01  cnf(contradiction,plain,
% 1.92/1.01      ( $false ),
% 1.92/1.01      inference(minisat,
% 1.92/1.01                [status(thm)],
% 1.92/1.01                [c_6892,c_5078,c_4915,c_4560,c_4550,c_3810,c_3271,c_3264,
% 1.92/1.01                 c_3256,c_3152,c_3067,c_3042,c_3039,c_1922,c_1847,c_45,
% 1.92/1.01                 c_36,c_43,c_38,c_42,c_39,c_41,c_40]) ).
% 1.92/1.01  
% 1.92/1.01  
% 1.92/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.92/1.01  
% 1.92/1.01  ------                               Statistics
% 1.92/1.01  
% 1.92/1.01  ------ General
% 1.92/1.01  
% 1.92/1.01  abstr_ref_over_cycles:                  0
% 1.92/1.01  abstr_ref_under_cycles:                 0
% 1.92/1.01  gc_basic_clause_elim:                   0
% 1.92/1.01  forced_gc_time:                         0
% 1.92/1.01  parsing_time:                           0.029
% 1.92/1.01  unif_index_cands_time:                  0.
% 1.92/1.01  unif_index_add_time:                    0.
% 1.92/1.01  orderings_time:                         0.
% 1.92/1.01  out_proof_time:                         0.016
% 1.92/1.01  total_time:                             0.257
% 1.92/1.01  num_of_symbols:                         71
% 1.92/1.01  num_of_terms:                           7944
% 1.92/1.01  
% 1.92/1.01  ------ Preprocessing
% 1.92/1.01  
% 1.92/1.01  num_of_splits:                          0
% 1.92/1.01  num_of_split_atoms:                     0
% 1.92/1.01  num_of_reused_defs:                     0
% 1.92/1.01  num_eq_ax_congr_red:                    48
% 1.92/1.01  num_of_sem_filtered_clauses:            5
% 1.92/1.01  num_of_subtypes:                        5
% 1.92/1.01  monotx_restored_types:                  0
% 1.92/1.01  sat_num_of_epr_types:                   0
% 1.92/1.01  sat_num_of_non_cyclic_types:            0
% 1.92/1.01  sat_guarded_non_collapsed_types:        2
% 1.92/1.01  num_pure_diseq_elim:                    0
% 1.92/1.01  simp_replaced_by:                       0
% 1.92/1.01  res_preprocessed:                       207
% 1.92/1.01  prep_upred:                             0
% 1.92/1.01  prep_unflattend:                        57
% 1.92/1.01  smt_new_axioms:                         0
% 1.92/1.01  pred_elim_cands:                        12
% 1.92/1.01  pred_elim:                              3
% 1.92/1.01  pred_elim_cl:                           4
% 1.92/1.01  pred_elim_cycles:                       9
% 1.92/1.01  merged_defs:                            0
% 1.92/1.01  merged_defs_ncl:                        0
% 1.92/1.01  bin_hyper_res:                          0
% 1.92/1.01  prep_cycles:                            4
% 1.92/1.01  pred_elim_time:                         0.021
% 1.92/1.01  splitting_time:                         0.
% 1.92/1.01  sem_filter_time:                        0.
% 1.92/1.01  monotx_time:                            0.
% 1.92/1.01  subtype_inf_time:                       0.
% 1.92/1.01  
% 1.92/1.01  ------ Problem properties
% 1.92/1.01  
% 1.92/1.01  clauses:                                37
% 1.92/1.01  conjectures:                            6
% 1.92/1.01  epr:                                    8
% 1.92/1.01  horn:                                   12
% 1.92/1.01  ground:                                 6
% 1.92/1.01  unary:                                  6
% 1.92/1.01  binary:                                 4
% 1.92/1.01  lits:                                   181
% 1.92/1.01  lits_eq:                                17
% 1.92/1.01  fd_pure:                                0
% 1.92/1.01  fd_pseudo:                              0
% 1.92/1.01  fd_cond:                                0
% 1.92/1.01  fd_pseudo_cond:                         7
% 1.92/1.01  ac_symbols:                             0
% 1.92/1.01  
% 1.92/1.01  ------ Propositional Solver
% 1.92/1.01  
% 1.92/1.01  prop_solver_calls:                      27
% 1.92/1.01  prop_fast_solver_calls:                 2540
% 1.92/1.01  smt_solver_calls:                       0
% 1.92/1.01  smt_fast_solver_calls:                  0
% 1.92/1.01  prop_num_of_clauses:                    1950
% 1.92/1.01  prop_preprocess_simplified:             8279
% 1.92/1.01  prop_fo_subsumed:                       79
% 1.92/1.01  prop_solver_time:                       0.
% 1.92/1.01  smt_solver_time:                        0.
% 1.92/1.01  smt_fast_solver_time:                   0.
% 1.92/1.01  prop_fast_solver_time:                  0.
% 1.92/1.01  prop_unsat_core_time:                   0.
% 1.92/1.01  
% 1.92/1.01  ------ QBF
% 1.92/1.01  
% 1.92/1.01  qbf_q_res:                              0
% 1.92/1.01  qbf_num_tautologies:                    0
% 1.92/1.01  qbf_prep_cycles:                        0
% 1.92/1.01  
% 1.92/1.01  ------ BMC1
% 1.92/1.01  
% 1.92/1.01  bmc1_current_bound:                     -1
% 1.92/1.01  bmc1_last_solved_bound:                 -1
% 1.92/1.01  bmc1_unsat_core_size:                   -1
% 1.92/1.01  bmc1_unsat_core_parents_size:           -1
% 1.92/1.01  bmc1_merge_next_fun:                    0
% 1.92/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.92/1.01  
% 1.92/1.01  ------ Instantiation
% 1.92/1.01  
% 1.92/1.01  inst_num_of_clauses:                    557
% 1.92/1.01  inst_num_in_passive:                    146
% 1.92/1.01  inst_num_in_active:                     365
% 1.92/1.01  inst_num_in_unprocessed:                46
% 1.92/1.01  inst_num_of_loops:                      380
% 1.92/1.01  inst_num_of_learning_restarts:          0
% 1.92/1.01  inst_num_moves_active_passive:          11
% 1.92/1.01  inst_lit_activity:                      0
% 1.92/1.01  inst_lit_activity_moves:                0
% 1.92/1.01  inst_num_tautologies:                   0
% 1.92/1.01  inst_num_prop_implied:                  0
% 1.92/1.01  inst_num_existing_simplified:           0
% 1.92/1.01  inst_num_eq_res_simplified:             0
% 1.92/1.01  inst_num_child_elim:                    0
% 1.92/1.01  inst_num_of_dismatching_blockings:      126
% 1.92/1.01  inst_num_of_non_proper_insts:           594
% 1.92/1.01  inst_num_of_duplicates:                 0
% 1.92/1.01  inst_inst_num_from_inst_to_res:         0
% 1.92/1.01  inst_dismatching_checking_time:         0.
% 1.92/1.01  
% 1.92/1.01  ------ Resolution
% 1.92/1.02  
% 1.92/1.02  res_num_of_clauses:                     0
% 1.92/1.02  res_num_in_passive:                     0
% 1.92/1.02  res_num_in_active:                      0
% 1.92/1.02  res_num_of_loops:                       211
% 1.92/1.02  res_forward_subset_subsumed:            58
% 1.92/1.02  res_backward_subset_subsumed:           0
% 1.92/1.02  res_forward_subsumed:                   0
% 1.92/1.02  res_backward_subsumed:                  0
% 1.92/1.02  res_forward_subsumption_resolution:     20
% 1.92/1.02  res_backward_subsumption_resolution:    0
% 1.92/1.02  res_clause_to_clause_subsumption:       369
% 1.92/1.02  res_orphan_elimination:                 0
% 1.92/1.02  res_tautology_del:                      86
% 1.92/1.02  res_num_eq_res_simplified:              0
% 1.92/1.02  res_num_sel_changes:                    0
% 1.92/1.02  res_moves_from_active_to_pass:          0
% 1.92/1.02  
% 1.92/1.02  ------ Superposition
% 1.92/1.02  
% 1.92/1.02  sup_time_total:                         0.
% 1.92/1.02  sup_time_generating:                    0.
% 1.92/1.02  sup_time_sim_full:                      0.
% 1.92/1.02  sup_time_sim_immed:                     0.
% 1.92/1.02  
% 1.92/1.02  sup_num_of_clauses:                     109
% 1.92/1.02  sup_num_in_active:                      75
% 1.92/1.02  sup_num_in_passive:                     34
% 1.92/1.02  sup_num_of_loops:                       75
% 1.92/1.02  sup_fw_superposition:                   51
% 1.92/1.02  sup_bw_superposition:                   35
% 1.92/1.02  sup_immediate_simplified:               19
% 1.92/1.02  sup_given_eliminated:                   0
% 1.92/1.02  comparisons_done:                       0
% 1.92/1.02  comparisons_avoided:                    3
% 1.92/1.02  
% 1.92/1.02  ------ Simplifications
% 1.92/1.02  
% 1.92/1.02  
% 1.92/1.02  sim_fw_subset_subsumed:                 3
% 1.92/1.02  sim_bw_subset_subsumed:                 1
% 1.92/1.02  sim_fw_subsumed:                        1
% 1.92/1.02  sim_bw_subsumed:                        0
% 1.92/1.02  sim_fw_subsumption_res:                 6
% 1.92/1.02  sim_bw_subsumption_res:                 0
% 1.92/1.02  sim_tautology_del:                      1
% 1.92/1.02  sim_eq_tautology_del:                   3
% 1.92/1.02  sim_eq_res_simp:                        1
% 1.92/1.02  sim_fw_demodulated:                     0
% 1.92/1.02  sim_bw_demodulated:                     1
% 1.92/1.02  sim_light_normalised:                   14
% 1.92/1.02  sim_joinable_taut:                      0
% 1.92/1.02  sim_joinable_simp:                      0
% 1.92/1.02  sim_ac_normalised:                      0
% 1.92/1.02  sim_smt_subsumption:                    0
% 1.92/1.02  
%------------------------------------------------------------------------------
