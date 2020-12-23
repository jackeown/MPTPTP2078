%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:12 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  225 (1602 expanded)
%              Number of clauses        :  140 ( 384 expanded)
%              Number of leaves         :   17 ( 416 expanded)
%              Depth                    :   30
%              Number of atoms          : 1198 (12006 expanded)
%              Number of equality atoms :  203 ( 549 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,sK4)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),sK4,k8_tmap_1(X0,sK4))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,sK4)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4)) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK3,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),X1,k8_tmap_1(sK3,X1))
            | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK3,X1)))
            | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1)) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
      | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) )
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f53,f52])).

fof(f91,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
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
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    ! [X2,X0] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f62,plain,(
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

fof(f94,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f94])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f101,plain,(
    ! [X2,X0] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f59,plain,(
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

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f96])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    ! [X2,X0] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ! [X2,X0] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

cnf(c_31,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_939,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_940,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_942,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_35])).

cnf(c_3463,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_942])).

cnf(c_3997,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3463])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_36])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_37,c_35])).

cnf(c_3453,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0_54) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1328])).

cnf(c_4007,plain,
    ( k7_tmap_1(sK3,X0_54) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3453])).

cnf(c_4472,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_3997,c_4007])).

cnf(c_28,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_32,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_462,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_463,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_467,plain,
    ( v2_struct_0(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK4,X0)
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_34])).

cnf(c_468,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_491,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_468,c_31])).

cnf(c_1159,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | sK4 != sK4
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_491])).

cnf(c_1160,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_258,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_31,c_25,c_24,c_18])).

cnf(c_259,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_909,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_33])).

cnf(c_910,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_1162,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_37,c_36,c_35,c_910])).

cnf(c_1163,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(renaming,[status(thm)],[c_1162])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_220,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_31])).

cnf(c_221,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_928,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_221,c_33])).

cnf(c_929,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_931,plain,
    ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_37,c_36,c_35,c_34])).

cnf(c_2130,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1163,c_931])).

cnf(c_3439,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(subtyping,[status(esa)],[c_2130])).

cnf(c_4021,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3439])).

cnf(c_912,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_910,c_37,c_36,c_35])).

cnf(c_3466,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_912])).

cnf(c_4124,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4021,c_3466])).

cnf(c_5036,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4472,c_4124])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_978,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_979,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_981,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_979,c_37,c_36,c_35])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_965,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_966,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_37,c_36,c_35])).

cnf(c_14,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_248,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_22])).

cnf(c_837,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_248,c_33])).

cnf(c_838,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_837])).

cnf(c_840,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_838,c_37,c_36,c_35])).

cnf(c_841,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_840])).

cnf(c_949,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_942,c_841])).

cnf(c_975,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_968,c_949])).

cnf(c_988,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_981,c_975])).

cnf(c_1556,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK3,sK4) != X0
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != X3
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != X5
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != X2
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_988])).

cnf(c_1557,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1556])).

cnf(c_871,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_872,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_1013,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_1014,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_444,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_954,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k8_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_955,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_957,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_37,c_36,c_35])).

cnf(c_1440,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK3,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_444,c_957])).

cnf(c_1441,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_1559,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_37,c_36,c_35,c_872,c_966,c_979,c_1014,c_1441])).

cnf(c_1560,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_1559])).

cnf(c_3440,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1560])).

cnf(c_4020,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3440])).

cnf(c_4113,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4020,c_3466])).

cnf(c_1443,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_37,c_36,c_35,c_1014])).

cnf(c_3448,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_1443])).

cnf(c_4012,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3448])).

cnf(c_4119,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4113,c_4012])).

cnf(c_40,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_941,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_1288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_37,c_35])).

cnf(c_3455,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0_54)) ),
    inference(subtyping,[status(esa)],[c_1292])).

cnf(c_4226,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3455])).

cnf(c_4227,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4226])).

cnf(c_16,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1251,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_1252,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1251])).

cnf(c_1256,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_37,c_35])).

cnf(c_3457,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_54),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1256])).

cnf(c_4003,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_54),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3457])).

cnf(c_4559,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3466,c_4003])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1305])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_37,c_35])).

cnf(c_3454,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))))) ),
    inference(subtyping,[status(esa)],[c_1310])).

cnf(c_4006,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3454])).

cnf(c_4660,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3466,c_4006])).

cnf(c_5471,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4119,c_40,c_941,c_4227,c_4559,c_4660])).

cnf(c_5473,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_5471,c_4472])).

cnf(c_5558,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4)
    | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5036,c_5473])).

cnf(c_5559,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5558])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_229,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_31])).

cnf(c_230,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_917,plain,
    ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_33])).

cnf(c_918,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_920,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_37,c_36,c_35,c_34])).

cnf(c_3465,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
    inference(subtyping,[status(esa)],[c_920])).

cnf(c_3995,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3465])).

cnf(c_4078,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3995,c_3466])).

cnf(c_5039,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4472,c_4078])).

cnf(c_29,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_857,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_858,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_860,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_37,c_36,c_35,c_34])).

cnf(c_950,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_942,c_860])).

cnf(c_3462,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
    inference(subtyping,[status(esa)],[c_950])).

cnf(c_3998,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3462])).

cnf(c_4067,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3998,c_3466])).

cnf(c_5040,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4472,c_4067])).

cnf(c_5562,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5559,c_5039,c_5040])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.00  
% 2.44/1.00  ------  iProver source info
% 2.44/1.00  
% 2.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.00  git: non_committed_changes: false
% 2.44/1.00  git: last_make_outside_of_git: false
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     num_symb
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       true
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  ------ Parsing...
% 2.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.00  ------ Proving...
% 2.44/1.00  ------ Problem Properties 
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  clauses                                 29
% 2.44/1.00  conjectures                             0
% 2.44/1.00  EPR                                     0
% 2.44/1.00  Horn                                    25
% 2.44/1.00  unary                                   14
% 2.44/1.00  binary                                  10
% 2.44/1.00  lits                                    60
% 2.44/1.00  lits eq                                 12
% 2.44/1.00  fd_pure                                 0
% 2.44/1.00  fd_pseudo                               0
% 2.44/1.00  fd_cond                                 3
% 2.44/1.00  fd_pseudo_cond                          0
% 2.44/1.00  AC symbols                              0
% 2.44/1.00  
% 2.44/1.00  ------ Schedule dynamic 5 is on 
% 2.44/1.00  
% 2.44/1.00  ------ no conjectures: strip conj schedule 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  Current options:
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     none
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       false
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00   Resolution empty clause
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f13,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f38,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f86,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f38])).
% 2.44/1.00  
% 2.44/1.00  fof(f14,conjecture,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f15,negated_conjecture,(
% 2.44/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 2.44/1.00    inference(negated_conjecture,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f39,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f15])).
% 2.44/1.00  
% 2.44/1.00  fof(f40,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f39])).
% 2.44/1.00  
% 2.44/1.00  fof(f53,plain,(
% 2.44/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),sK4,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4))) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f52,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),X1,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1))) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f54,plain,(
% 2.44/1.00    ((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f53,f52])).
% 2.44/1.00  
% 2.44/1.00  fof(f91,plain,(
% 2.44/1.00    m1_pre_topc(sK4,sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f89,plain,(
% 2.44/1.00    l1_pre_topc(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f5,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f22,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f5])).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f61,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f88,plain,(
% 2.44/1.00    v2_pre_topc(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f87,plain,(
% 2.44/1.00    ~v2_struct_0(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f12,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f36,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f36])).
% 2.44/1.00  
% 2.44/1.00  fof(f84,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f99,plain,(
% 2.44/1.00    ( ! [X2,X0] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f84])).
% 2.44/1.00  
% 2.44/1.00  fof(f92,plain,(
% 2.44/1.00    ~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f90,plain,(
% 2.44/1.00    ~v2_struct_0(sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f54])).
% 2.44/1.00  
% 2.44/1.00  fof(f6,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f24,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f6])).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f24])).
% 2.44/1.00  
% 2.44/1.00  fof(f44,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f25])).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(rectify,[],[f44])).
% 2.44/1.00  
% 2.44/1.00  fof(f46,plain,(
% 2.44/1.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f47,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 2.44/1.00  
% 2.44/1.00  fof(f62,plain,(
% 2.44/1.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f47])).
% 2.44/1.00  
% 2.44/1.00  fof(f94,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f62])).
% 2.44/1.00  
% 2.44/1.00  fof(f95,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f94])).
% 2.44/1.00  
% 2.44/1.00  fof(f11,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f34,plain,(
% 2.44/1.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f11])).
% 2.44/1.00  
% 2.44/1.00  fof(f35,plain,(
% 2.44/1.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f80,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f35])).
% 2.44/1.00  
% 2.44/1.00  fof(f81,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f35])).
% 2.44/1.00  
% 2.44/1.00  fof(f9,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f30,plain,(
% 2.44/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f31,plain,(
% 2.44/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f30])).
% 2.44/1.00  
% 2.44/1.00  fof(f75,plain,(
% 2.44/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f31])).
% 2.44/1.00  
% 2.44/1.00  fof(f82,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f101,plain,(
% 2.44/1.00    ( ! [X2,X0] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f82])).
% 2.44/1.00  
% 2.44/1.00  fof(f4,axiom,(
% 2.44/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.44/1.00    inference(ennf_transformation,[],[f4])).
% 2.44/1.00  
% 2.44/1.00  fof(f21,plain,(
% 2.44/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.44/1.00    inference(flattening,[],[f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.44/1.00    inference(nnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f59,plain,(
% 2.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f43])).
% 2.44/1.00  
% 2.44/1.00  fof(f10,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f32,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f33,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f78,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f76,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f7,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f26])).
% 2.44/1.00  
% 2.44/1.00  fof(f48,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(rectify,[],[f48])).
% 2.44/1.00  
% 2.44/1.00  fof(f50,plain,(
% 2.44/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f51,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 2.44/1.00  
% 2.44/1.00  fof(f66,plain,(
% 2.44/1.00    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f51])).
% 2.44/1.00  
% 2.44/1.00  fof(f96,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f66])).
% 2.44/1.00  
% 2.44/1.00  fof(f97,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f96])).
% 2.44/1.00  
% 2.44/1.00  fof(f77,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f16,plain,(
% 2.44/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f55,plain,(
% 2.44/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f16])).
% 2.44/1.00  
% 2.44/1.00  fof(f2,axiom,(
% 2.44/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f17,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f2])).
% 2.44/1.00  
% 2.44/1.00  fof(f18,plain,(
% 2.44/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f79,plain,(
% 2.44/1.00    ( ! [X0,X1] : (~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f35])).
% 2.44/1.00  
% 2.44/1.00  fof(f8,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f8])).
% 2.44/1.00  
% 2.44/1.00  fof(f29,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f70,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f71,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f72,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f85,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f98,plain,(
% 2.44/1.00    ( ! [X2,X0] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f85])).
% 2.44/1.00  
% 2.44/1.00  fof(f83,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f100,plain,(
% 2.44/1.00    ( ! [X2,X0] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f83])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_31,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_33,negated_conjecture,
% 2.44/1.00      ( m1_pre_topc(sK4,sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_939,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | sK4 != X0
% 2.44/1.00      | sK3 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_940,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_939]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_35,negated_conjecture,
% 2.44/1.00      ( l1_pre_topc(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_942,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_940,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3463,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_942]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3997,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3463]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_6,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_36,negated_conjecture,
% 2.44/1.00      ( v2_pre_topc(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1323,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 2.44/1.00      | sK3 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_36]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1324,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3)
% 2.44/1.00      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1323]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_37,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1328,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1324,c_37,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3453,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | k7_tmap_1(sK3,X0_54) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1328]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4007,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,X0_54) = k6_partfun1(u1_struct_0(sK3))
% 2.44/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3453]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4472,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3997,c_4007]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_28,plain,
% 2.44/1.00      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_pre_topc(X1,X0)
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_32,negated_conjecture,
% 2.44/1.00      ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK4,k8_tmap_1(sK3,sK4))
% 2.44/1.00      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_462,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
% 2.44/1.00      | sK4 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_463,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(sK4)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_34,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_467,plain,
% 2.44/1.00      ( v2_struct_0(X0)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.44/1.00      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_463,c_34]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_468,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_467]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_491,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_pre_topc(sK4,X0)
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_468,c_31]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1159,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 2.44/1.00      | sK4 != sK4
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_491]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1160,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3)
% 2.44/1.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1159]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.44/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_258,plain,
% 2.44/1.00      ( ~ l1_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_10,c_31,c_25,c_24,c_18]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_259,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_258]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_909,plain,
% 2.44/1.00      ( ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_259,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_910,plain,
% 2.44/1.00      ( ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3)
% 2.44/1.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_909]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1162,plain,
% 2.44/1.00      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1160,c_37,c_36,c_35,c_910]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1163,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 2.44/1.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_1162]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_30,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_220,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_30,c_31]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_221,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_220]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_928,plain,
% 2.44/1.00      ( ~ v2_pre_topc(X0)
% 2.44/1.00      | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_221,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_929,plain,
% 2.44/1.00      ( ~ v2_pre_topc(sK3)
% 2.44/1.00      | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4))
% 2.44/1.00      | v2_struct_0(sK4)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_928]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_931,plain,
% 2.44/1.00      ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_929,c_37,c_36,c_35,c_34]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2130,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_1163,c_931]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3439,plain,
% 2.44/1.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_2130]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4021,plain,
% 2.44/1.00      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3439]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_912,plain,
% 2.44/1.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_910,c_37,c_36,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3466,plain,
% 2.44/1.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_912]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4124,plain,
% 2.44/1.00      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4021,c_3466]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5036,plain,
% 2.44/1.00      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 2.44/1.00      | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4472,c_4124]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5,plain,
% 2.44/1.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.44/1.00      | ~ v1_funct_2(X5,X2,X3)
% 2.44/1.00      | ~ v1_funct_2(X4,X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.44/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.44/1.00      | ~ v1_funct_1(X5)
% 2.44/1.00      | ~ v1_funct_1(X4)
% 2.44/1.00      | v1_xboole_0(X1)
% 2.44/1.00      | v1_xboole_0(X3)
% 2.44/1.00      | X4 = X5 ),
% 2.44/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_21,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_978,plain,
% 2.44/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_979,plain,
% 2.44/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_978]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_981,plain,
% 2.44/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_979,c_37,c_36,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_965,plain,
% 2.44/1.00      ( ~ v2_pre_topc(X0)
% 2.44/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_966,plain,
% 2.44/1.00      ( ~ v2_pre_topc(sK3)
% 2.44/1.00      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_965]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_968,plain,
% 2.44/1.00      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_966,c_37,c_36,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_14,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.44/1.00      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.44/1.00      | ~ m1_pre_topc(X1,X0)
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,plain,
% 2.44/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.44/1.00      | ~ m1_pre_topc(X1,X0)
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_248,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_pre_topc(X1,X0)
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_14,c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_837,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_248,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_838,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_837]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_840,plain,
% 2.44/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_838,c_37,c_36,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_841,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_840]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_949,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_942,c_841]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_975,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.44/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_968,c_949]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_988,plain,
% 2.44/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 2.44/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_981,c_975]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1556,plain,
% 2.44/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.44/1.00      | ~ v1_funct_2(X3,X4,X5)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.44/1.00      | ~ v1_funct_1(X0)
% 2.44/1.00      | ~ v1_funct_1(X3)
% 2.44/1.00      | v1_xboole_0(X2)
% 2.44/1.00      | v1_xboole_0(X5)
% 2.44/1.00      | X3 = X0
% 2.44/1.00      | k9_tmap_1(sK3,sK4) != X0
% 2.44/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != X3
% 2.44/1.00      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != X5
% 2.44/1.00      | u1_struct_0(k8_tmap_1(sK3,sK4)) != X2
% 2.44/1.00      | u1_struct_0(sK3) != X4
% 2.44/1.00      | u1_struct_0(sK3) != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_988]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1557,plain,
% 2.44/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.44/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.44/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.44/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1556]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_871,plain,
% 2.44/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_872,plain,
% 2.44/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_871]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1013,plain,
% 2.44/1.00      ( ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1014,plain,
% 2.44/1.00      ( ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | l1_pre_topc(k8_tmap_1(sK3,sK4))
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1013]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_0,plain,
% 2.44/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1,plain,
% 2.44/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_444,plain,
% 2.44/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_26,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v2_struct_0(k8_tmap_1(X1,X0))
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_954,plain,
% 2.44/1.00      ( ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ v2_struct_0(k8_tmap_1(X0,X1))
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_955,plain,
% 2.44/1.00      ( ~ v2_pre_topc(sK3)
% 2.44/1.00      | ~ v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_954]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_957,plain,
% 2.44/1.00      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_955,c_37,c_36,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1440,plain,
% 2.44/1.00      ( ~ v1_xboole_0(u1_struct_0(X0))
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | k8_tmap_1(sK3,sK4) != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_444,c_957]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1441,plain,
% 2.44/1.00      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.44/1.00      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1440]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1559,plain,
% 2.44/1.00      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.44/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1557,c_37,c_36,c_35,c_872,c_966,c_979,c_1014,c_1441]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1560,plain,
% 2.44/1.00      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.44/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_1559]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3440,plain,
% 2.44/1.00      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.44/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1560]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4020,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.44/1.00      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3440]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4113,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.44/1.00      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4020,c_3466]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1443,plain,
% 2.44/1.00      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1441,c_37,c_36,c_35,c_1014]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3448,plain,
% 2.44/1.00      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1443]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4012,plain,
% 2.44/1.00      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3448]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4119,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.44/1.00      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 2.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4113,c_4012]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_40,plain,
% 2.44/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_941,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.44/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_17,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1287,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | sK3 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1288,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,X0))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1287]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1292,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,X0)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1288,c_37,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3455,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,X0_54)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1292]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4226,plain,
% 2.44/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_3455]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4227,plain,
% 2.44/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_4226]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_16,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1251,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1252,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1251]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1256,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1252,c_37,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3457,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0_54),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54)))
% 2.44/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1256]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4003,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0_54),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))) = iProver_top
% 2.44/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3457]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4559,plain,
% 2.44/1.00      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 2.44/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3466,c_4003]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_15,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1305,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | sK3 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1306,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_1305]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1310,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1306,c_37,c_35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3454,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_1310]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4006,plain,
% 2.44/1.00      ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | m1_subset_1(k7_tmap_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_54))))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3454]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4660,plain,
% 2.44/1.00      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 2.44/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3466,c_4006]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5471,plain,
% 2.44/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4119,c_40,c_941,c_4227,c_4559,c_4660]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5473,plain,
% 2.44/1.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_5471,c_4472]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5558,plain,
% 2.44/1.00      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4)
% 2.44/1.00      | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_5036,c_5473]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5559,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.44/1.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top ),
% 2.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_5558]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_27,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_229,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.44/1.00      | ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_27,c_31]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_230,plain,
% 2.44/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.44/1.00      | m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X0))))))
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_229]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_917,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_230,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_918,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK4)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_917]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_920,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_918,c_37,c_36,c_35,c_34]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3465,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_920]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3995,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3465]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4078,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_3995,c_3466]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5039,plain,
% 2.44/1.00      ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4472,c_4078]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_29,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 2.44/1.00      | ~ m1_pre_topc(X1,X0)
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_857,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ v2_pre_topc(X0)
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ l1_pre_topc(X0)
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK3 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_858,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | v2_struct_0(sK4)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ l1_pre_topc(sK3) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_857]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_860,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.44/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_858,c_37,c_36,c_35,c_34]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_950,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
% 2.44/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_942,c_860]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3462,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_950]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3998,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3462]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4067,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_3998,c_3466]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5040,plain,
% 2.44/1.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4472,c_4067]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5562,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(forward_subsumption_resolution,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5559,c_5039,c_5040]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.014
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.017
% 2.44/1.00  total_time:                             0.222
% 2.44/1.00  num_of_symbols:                         63
% 2.44/1.00  num_of_terms:                           4599
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    12
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        3
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        1
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       164
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        133
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        4
% 2.44/1.00  pred_elim:                              8
% 2.44/1.00  pred_elim_cl:                           7
% 2.44/1.00  pred_elim_cycles:                       15
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.092
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                29
% 2.44/1.00  conjectures:                            0
% 2.44/1.00  epr:                                    0
% 2.44/1.00  horn:                                   25
% 2.44/1.00  ground:                                 18
% 2.44/1.00  unary:                                  14
% 2.44/1.00  binary:                                 10
% 2.44/1.00  lits:                                   60
% 2.44/1.00  lits_eq:                                12
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                3
% 2.44/1.00  fd_pseudo_cond:                         0
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      27
% 2.44/1.00  prop_fast_solver_calls:                 1818
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1250
% 2.44/1.00  prop_preprocess_simplified:             5093
% 2.44/1.00  prop_fo_subsumed:                       105
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    308
% 2.44/1.00  inst_num_in_passive:                    71
% 2.44/1.00  inst_num_in_active:                     224
% 2.44/1.00  inst_num_in_unprocessed:                13
% 2.44/1.00  inst_num_of_loops:                      230
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          3
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      23
% 2.44/1.00  inst_num_of_non_proper_insts:           243
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       168
% 2.44/1.00  res_forward_subset_subsumed:            54
% 2.44/1.00  res_backward_subset_subsumed:           3
% 2.44/1.00  res_forward_subsumed:                   2
% 2.44/1.00  res_backward_subsumed:                  1
% 2.44/1.00  res_forward_subsumption_resolution:     15
% 2.44/1.00  res_backward_subsumption_resolution:    4
% 2.44/1.00  res_clause_to_clause_subsumption:       374
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      87
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     40
% 2.44/1.00  sup_num_in_active:                      30
% 2.44/1.00  sup_num_in_passive:                     10
% 2.44/1.00  sup_num_of_loops:                       44
% 2.44/1.00  sup_fw_superposition:                   13
% 2.44/1.00  sup_bw_superposition:                   7
% 2.44/1.00  sup_immediate_simplified:               4
% 2.44/1.00  sup_given_eliminated:                   0
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 2
% 2.44/1.00  sim_bw_subset_subsumed:                 1
% 2.44/1.00  sim_fw_subsumed:                        0
% 2.44/1.00  sim_bw_subsumed:                        0
% 2.44/1.00  sim_fw_subsumption_res:                 3
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      0
% 2.44/1.00  sim_eq_tautology_del:                   2
% 2.44/1.00  sim_eq_res_simp:                        1
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     14
% 2.44/1.00  sim_light_normalised:                   9
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
