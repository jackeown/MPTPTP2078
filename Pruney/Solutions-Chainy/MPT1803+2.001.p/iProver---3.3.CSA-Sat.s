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
% DateTime   : Thu Dec  3 12:24:07 EST 2020

% Result     : CounterSatisfiable 1.96s
% Output     : Saturation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  275 (2022 expanded)
%              Number of clauses        :  174 ( 458 expanded)
%              Number of leaves         :   33 ( 612 expanded)
%              Depth                    :   27
%              Number of atoms          : 1564 (12893 expanded)
%              Number of equality atoms :  241 ( 528 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   20 (   5 average)
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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK5)
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK4,k8_tmap_1(X0,sK4),k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),X2)
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK3,X1),k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f60,f59,f58])).

fof(f100,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

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
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f35])).

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
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X2,X0] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X1,X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f36])).

fof(f108,plain,(
    ! [X2,X0] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

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
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    ! [X2,X0] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

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
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,(
    ! [X2,X0] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP0(X1,X0,X2)
              <=> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f41,f44])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP0(X1,X0,X2)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X0,X1,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ sP0(X1,X0,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP0(X1,X0,X2)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ sP0(X1,X0,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X0,X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_tmap_1(X0,X1,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP0(X1,X0,X2)
                  | ( ~ r1_tmap_1(X0,X1,X2,sK2(X0,X1,X2))
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ sP0(X1,X0,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X0,X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ sP0(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f105,plain,(
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
    inference(equality_resolution,[],[f104])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f23])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_422,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_421,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X3,X1,X4)
    | X3 != X0
    | X4 != X2 ),
    theory(equality)).

cnf(c_418,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_413,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_412,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_408,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_407,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_406,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_404,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_403,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_402,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2106,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_25,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1410,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_1411,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1410])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1413,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1411,c_38])).

cnf(c_2103,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1413])).

cnf(c_2290,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_39])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1756])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_40,c_38])).

cnf(c_2099,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1761])).

cnf(c_2293,plain,
    ( k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2099])).

cnf(c_2413,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_2290,c_2293])).

cnf(c_21,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2)
    | ~ v5_pre_topc(X2,X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_481,plain,
    ( sP0(X0,X1,X2)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X3,X4)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | X1 != X3
    | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X2
    | k6_tmap_1(X4,u1_struct_0(X3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_482,plain,
    ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_22,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_20,plain,
    ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_486,plain,
    ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_22,c_20])).

cnf(c_23,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_242,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_25])).

cnf(c_508,plain,
    ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_486,c_242,c_25])).

cnf(c_33,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ sP0(X1,X0,X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_628,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != X2
    | k8_tmap_1(sK3,sK4) != X0
    | sK5 != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_34])).

cnf(c_629,plain,
    ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_631,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_37,c_35])).

cnf(c_632,plain,
    ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_631])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_653,plain,
    ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_632,c_30,c_27,c_29])).

cnf(c_915,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4)
    | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_508,c_653])).

cnf(c_916,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_920,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_37])).

cnf(c_921,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_920])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_948,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_921,c_0,c_2])).

cnf(c_1646,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | sK3 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_948])).

cnf(c_1647,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1646])).

cnf(c_959,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_10,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_261,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_25,c_18,c_17,c_11])).

cnf(c_262,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_261])).

cnf(c_1391,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_262,c_36])).

cnf(c_1392,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1391])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1421,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k8_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_1422,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1454,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_1455,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1454])).

cnf(c_1465,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_1466,plain,
    ( v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1465])).

cnf(c_1649,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1647,c_40,c_39,c_38,c_36,c_959,c_1392,c_1422,c_1455,c_1466])).

cnf(c_2100,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(subtyping,[status(esa)],[c_1649])).

cnf(c_1394,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1392,c_40,c_39,c_38])).

cnf(c_2104,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1394])).

cnf(c_2314,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(light_normalisation,[status(thm)],[c_2100,c_2104])).

cnf(c_2607,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
    inference(demodulation,[status(thm)],[c_2413,c_2314])).

cnf(c_856,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | X3 != X1
    | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X0
    | k6_tmap_1(X4,u1_struct_0(X3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_508])).

cnf(c_857,plain,
    ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_1552,plain,
    ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_857,c_36])).

cnf(c_1553,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1552])).

cnf(c_1555,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1553,c_40,c_39,c_38,c_37])).

cnf(c_2102,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
    inference(subtyping,[status(esa)],[c_1555])).

cnf(c_2291,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_2321,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2291,c_2104])).

cnf(c_2606,plain,
    ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2413,c_2321])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_462,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_pre_topc(X6,X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(X7)
    | ~ v2_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_528,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_15,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_14,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_532,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k3_struct_0(X0))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_15,c_14,c_462])).

cnf(c_533,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_560,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_533,c_16])).

cnf(c_1574,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_36])).

cnf(c_1575,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1574])).

cnf(c_1577,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1575,c_40,c_39,c_38,c_37])).

cnf(c_1716,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_462,c_1577])).

cnf(c_1468,plain,
    ( l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1466,c_40,c_39,c_38])).

cnf(c_1842,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | v2_struct_0(X0)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | k8_tmap_1(sK3,sK4) != X0
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_1716,c_1468])).

cnf(c_1843,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1842])).

cnf(c_1845,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1843,c_40,c_39,c_38,c_1422])).

cnf(c_1846,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_struct_0(sK3))
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1845])).

cnf(c_1399,plain,
    ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_242,c_36])).

cnf(c_1400,plain,
    ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1399])).

cnf(c_1402,plain,
    ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1400,c_40,c_39,c_38,c_37])).

cnf(c_1930,plain,
    ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_1846,c_1402])).

cnf(c_832,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | X3 != X1
    | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X0
    | k6_tmap_1(X4,u1_struct_0(X3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_508])).

cnf(c_833,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_1563,plain,
    ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_833,c_36])).

cnf(c_1564,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1563])).

cnf(c_1566,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_40,c_39,c_38,c_37])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1930,c_1566])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1972])).

cnf(c_2296,plain,
    ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_2324,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2296,c_2104])).

cnf(c_2605,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k3_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2413,c_2324])).

cnf(c_1541,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_36])).

cnf(c_1542,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1541])).

cnf(c_1544,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_39,c_38])).

cnf(c_1530,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_36])).

cnf(c_1531,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1530])).

cnf(c_1533,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1531,c_38])).

cnf(c_1457,plain,
    ( v2_pre_topc(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1455,c_40,c_39,c_38])).

cnf(c_1424,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_40,c_39,c_38])).

cnf(c_32,plain,
    ( sP0(X0,X1,X2)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | m1_subset_1(sK2(X1,X0,X2),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_880,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4)
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != X0
    | k8_tmap_1(sK3,sK4) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_653])).

cnf(c_881,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_883,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_37])).

cnf(c_884,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_1660,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1424,c_884])).

cnf(c_1668,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1457,c_1660])).

cnf(c_1672,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1468,c_1668])).

cnf(c_1688,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1672])).

cnf(c_1692,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1544,c_1688])).

cnf(c_1432,plain,
    ( v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_1433,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1432])).

cnf(c_1435,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1433,c_40,c_39,c_38])).

cnf(c_1947,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1692,c_1435])).

cnf(c_1597,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_1598,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1597])).

cnf(c_1600,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_40,c_39,c_38])).

cnf(c_1992,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1947,c_1600])).

cnf(c_2031,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_1992])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_2031])).

cnf(c_2297,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_1544])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1792])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1793,c_38,c_37,c_1531])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4)))
    | k7_tmap_1(sK4,X0_57) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1797])).

cnf(c_2295,plain,
    ( k7_tmap_1(sK4,X0_57) = k6_partfun1(u1_struct_0(sK4))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(sK3,sK4) != X1
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_1457])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | k7_tmap_1(k8_tmap_1(sK3,sK4),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_1774])).

cnf(c_1779,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
    | k7_tmap_1(k8_tmap_1(sK3,sK4),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1775,c_40,c_39,c_38,c_1422,c_1466])).

cnf(c_2098,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
    | k7_tmap_1(k8_tmap_1(sK3,sK4),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_1779])).

cnf(c_2294,plain,
    ( k7_tmap_1(k8_tmap_1(sK3,sK4),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2098])).

cnf(c_1608,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_1609,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1608])).

cnf(c_1611,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_40,c_39,c_38])).

cnf(c_2101,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(subtyping,[status(esa)],[c_1611])).

cnf(c_2292,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2101])).

cnf(c_2105,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_2289,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.96/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/0.98  
% 1.96/0.98  ------  iProver source info
% 1.96/0.98  
% 1.96/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.96/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/0.98  git: non_committed_changes: false
% 1.96/0.98  git: last_make_outside_of_git: false
% 1.96/0.98  
% 1.96/0.98  ------ 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options
% 1.96/0.98  
% 1.96/0.98  --out_options                           all
% 1.96/0.98  --tptp_safe_out                         true
% 1.96/0.98  --problem_path                          ""
% 1.96/0.98  --include_path                          ""
% 1.96/0.98  --clausifier                            res/vclausify_rel
% 1.96/0.98  --clausifier_options                    --mode clausify
% 1.96/0.98  --stdin                                 false
% 1.96/0.98  --stats_out                             all
% 1.96/0.98  
% 1.96/0.98  ------ General Options
% 1.96/0.98  
% 1.96/0.98  --fof                                   false
% 1.96/0.98  --time_out_real                         305.
% 1.96/0.98  --time_out_virtual                      -1.
% 1.96/0.98  --symbol_type_check                     false
% 1.96/0.98  --clausify_out                          false
% 1.96/0.98  --sig_cnt_out                           false
% 1.96/0.98  --trig_cnt_out                          false
% 1.96/0.98  --trig_cnt_out_tolerance                1.
% 1.96/0.98  --trig_cnt_out_sk_spl                   false
% 1.96/0.98  --abstr_cl_out                          false
% 1.96/0.98  
% 1.96/0.98  ------ Global Options
% 1.96/0.98  
% 1.96/0.98  --schedule                              default
% 1.96/0.98  --add_important_lit                     false
% 1.96/0.98  --prop_solver_per_cl                    1000
% 1.96/0.98  --min_unsat_core                        false
% 1.96/0.98  --soft_assumptions                      false
% 1.96/0.98  --soft_lemma_size                       3
% 1.96/0.98  --prop_impl_unit_size                   0
% 1.96/0.98  --prop_impl_unit                        []
% 1.96/0.98  --share_sel_clauses                     true
% 1.96/0.98  --reset_solvers                         false
% 1.96/0.98  --bc_imp_inh                            [conj_cone]
% 1.96/0.98  --conj_cone_tolerance                   3.
% 1.96/0.98  --extra_neg_conj                        none
% 1.96/0.98  --large_theory_mode                     true
% 1.96/0.98  --prolific_symb_bound                   200
% 1.96/0.98  --lt_threshold                          2000
% 1.96/0.98  --clause_weak_htbl                      true
% 1.96/0.98  --gc_record_bc_elim                     false
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing Options
% 1.96/0.98  
% 1.96/0.98  --preprocessing_flag                    true
% 1.96/0.98  --time_out_prep_mult                    0.1
% 1.96/0.98  --splitting_mode                        input
% 1.96/0.98  --splitting_grd                         true
% 1.96/0.98  --splitting_cvd                         false
% 1.96/0.98  --splitting_cvd_svl                     false
% 1.96/0.98  --splitting_nvd                         32
% 1.96/0.98  --sub_typing                            true
% 1.96/0.98  --prep_gs_sim                           true
% 1.96/0.98  --prep_unflatten                        true
% 1.96/0.98  --prep_res_sim                          true
% 1.96/0.98  --prep_upred                            true
% 1.96/0.98  --prep_sem_filter                       exhaustive
% 1.96/0.98  --prep_sem_filter_out                   false
% 1.96/0.98  --pred_elim                             true
% 1.96/0.98  --res_sim_input                         true
% 1.96/0.98  --eq_ax_congr_red                       true
% 1.96/0.98  --pure_diseq_elim                       true
% 1.96/0.98  --brand_transform                       false
% 1.96/0.98  --non_eq_to_eq                          false
% 1.96/0.98  --prep_def_merge                        true
% 1.96/0.98  --prep_def_merge_prop_impl              false
% 1.96/0.98  --prep_def_merge_mbd                    true
% 1.96/0.98  --prep_def_merge_tr_red                 false
% 1.96/0.98  --prep_def_merge_tr_cl                  false
% 1.96/0.98  --smt_preprocessing                     true
% 1.96/0.98  --smt_ac_axioms                         fast
% 1.96/0.98  --preprocessed_out                      false
% 1.96/0.98  --preprocessed_stats                    false
% 1.96/0.98  
% 1.96/0.98  ------ Abstraction refinement Options
% 1.96/0.98  
% 1.96/0.98  --abstr_ref                             []
% 1.96/0.98  --abstr_ref_prep                        false
% 1.96/0.98  --abstr_ref_until_sat                   false
% 1.96/0.98  --abstr_ref_sig_restrict                funpre
% 1.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.98  --abstr_ref_under                       []
% 1.96/0.98  
% 1.96/0.98  ------ SAT Options
% 1.96/0.98  
% 1.96/0.98  --sat_mode                              false
% 1.96/0.98  --sat_fm_restart_options                ""
% 1.96/0.98  --sat_gr_def                            false
% 1.96/0.98  --sat_epr_types                         true
% 1.96/0.98  --sat_non_cyclic_types                  false
% 1.96/0.98  --sat_finite_models                     false
% 1.96/0.98  --sat_fm_lemmas                         false
% 1.96/0.98  --sat_fm_prep                           false
% 1.96/0.98  --sat_fm_uc_incr                        true
% 1.96/0.98  --sat_out_model                         small
% 1.96/0.98  --sat_out_clauses                       false
% 1.96/0.98  
% 1.96/0.98  ------ QBF Options
% 1.96/0.98  
% 1.96/0.98  --qbf_mode                              false
% 1.96/0.98  --qbf_elim_univ                         false
% 1.96/0.98  --qbf_dom_inst                          none
% 1.96/0.98  --qbf_dom_pre_inst                      false
% 1.96/0.98  --qbf_sk_in                             false
% 1.96/0.98  --qbf_pred_elim                         true
% 1.96/0.98  --qbf_split                             512
% 1.96/0.98  
% 1.96/0.98  ------ BMC1 Options
% 1.96/0.98  
% 1.96/0.98  --bmc1_incremental                      false
% 1.96/0.98  --bmc1_axioms                           reachable_all
% 1.96/0.98  --bmc1_min_bound                        0
% 1.96/0.98  --bmc1_max_bound                        -1
% 1.96/0.98  --bmc1_max_bound_default                -1
% 1.96/0.98  --bmc1_symbol_reachability              true
% 1.96/0.98  --bmc1_property_lemmas                  false
% 1.96/0.98  --bmc1_k_induction                      false
% 1.96/0.98  --bmc1_non_equiv_states                 false
% 1.96/0.98  --bmc1_deadlock                         false
% 1.96/0.98  --bmc1_ucm                              false
% 1.96/0.98  --bmc1_add_unsat_core                   none
% 1.96/0.98  --bmc1_unsat_core_children              false
% 1.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.98  --bmc1_out_stat                         full
% 1.96/0.98  --bmc1_ground_init                      false
% 1.96/0.98  --bmc1_pre_inst_next_state              false
% 1.96/0.98  --bmc1_pre_inst_state                   false
% 1.96/0.98  --bmc1_pre_inst_reach_state             false
% 1.96/0.98  --bmc1_out_unsat_core                   false
% 1.96/0.98  --bmc1_aig_witness_out                  false
% 1.96/0.98  --bmc1_verbose                          false
% 1.96/0.98  --bmc1_dump_clauses_tptp                false
% 1.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.98  --bmc1_dump_file                        -
% 1.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.98  --bmc1_ucm_extend_mode                  1
% 1.96/0.98  --bmc1_ucm_init_mode                    2
% 1.96/0.98  --bmc1_ucm_cone_mode                    none
% 1.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.98  --bmc1_ucm_relax_model                  4
% 1.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.98  --bmc1_ucm_layered_model                none
% 1.96/0.98  --bmc1_ucm_max_lemma_size               10
% 1.96/0.98  
% 1.96/0.98  ------ AIG Options
% 1.96/0.98  
% 1.96/0.98  --aig_mode                              false
% 1.96/0.98  
% 1.96/0.98  ------ Instantiation Options
% 1.96/0.98  
% 1.96/0.98  --instantiation_flag                    true
% 1.96/0.98  --inst_sos_flag                         false
% 1.96/0.98  --inst_sos_phase                        true
% 1.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel_side                     num_symb
% 1.96/0.98  --inst_solver_per_active                1400
% 1.96/0.98  --inst_solver_calls_frac                1.
% 1.96/0.98  --inst_passive_queue_type               priority_queues
% 1.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.98  --inst_passive_queues_freq              [25;2]
% 1.96/0.98  --inst_dismatching                      true
% 1.96/0.98  --inst_eager_unprocessed_to_passive     true
% 1.96/0.98  --inst_prop_sim_given                   true
% 1.96/0.98  --inst_prop_sim_new                     false
% 1.96/0.98  --inst_subs_new                         false
% 1.96/0.98  --inst_eq_res_simp                      false
% 1.96/0.98  --inst_subs_given                       false
% 1.96/0.98  --inst_orphan_elimination               true
% 1.96/0.98  --inst_learning_loop_flag               true
% 1.96/0.98  --inst_learning_start                   3000
% 1.96/0.98  --inst_learning_factor                  2
% 1.96/0.98  --inst_start_prop_sim_after_learn       3
% 1.96/0.98  --inst_sel_renew                        solver
% 1.96/0.98  --inst_lit_activity_flag                true
% 1.96/0.98  --inst_restr_to_given                   false
% 1.96/0.98  --inst_activity_threshold               500
% 1.96/0.98  --inst_out_proof                        true
% 1.96/0.98  
% 1.96/0.98  ------ Resolution Options
% 1.96/0.98  
% 1.96/0.98  --resolution_flag                       true
% 1.96/0.98  --res_lit_sel                           adaptive
% 1.96/0.98  --res_lit_sel_side                      none
% 1.96/0.98  --res_ordering                          kbo
% 1.96/0.98  --res_to_prop_solver                    active
% 1.96/0.98  --res_prop_simpl_new                    false
% 1.96/0.98  --res_prop_simpl_given                  true
% 1.96/0.98  --res_passive_queue_type                priority_queues
% 1.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.98  --res_passive_queues_freq               [15;5]
% 1.96/0.98  --res_forward_subs                      full
% 1.96/0.98  --res_backward_subs                     full
% 1.96/0.98  --res_forward_subs_resolution           true
% 1.96/0.98  --res_backward_subs_resolution          true
% 1.96/0.98  --res_orphan_elimination                true
% 1.96/0.98  --res_time_limit                        2.
% 1.96/0.98  --res_out_proof                         true
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Options
% 1.96/0.98  
% 1.96/0.98  --superposition_flag                    true
% 1.96/0.98  --sup_passive_queue_type                priority_queues
% 1.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.98  --demod_completeness_check              fast
% 1.96/0.98  --demod_use_ground                      true
% 1.96/0.98  --sup_to_prop_solver                    passive
% 1.96/0.98  --sup_prop_simpl_new                    true
% 1.96/0.98  --sup_prop_simpl_given                  true
% 1.96/0.98  --sup_fun_splitting                     false
% 1.96/0.98  --sup_smt_interval                      50000
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Simplification Setup
% 1.96/0.98  
% 1.96/0.98  --sup_indices_passive                   []
% 1.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_full_bw                           [BwDemod]
% 1.96/0.98  --sup_immed_triv                        [TrivRules]
% 1.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_immed_bw_main                     []
% 1.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  
% 1.96/0.98  ------ Combination Options
% 1.96/0.98  
% 1.96/0.98  --comb_res_mult                         3
% 1.96/0.98  --comb_sup_mult                         2
% 1.96/0.98  --comb_inst_mult                        10
% 1.96/0.98  
% 1.96/0.98  ------ Debug Options
% 1.96/0.98  
% 1.96/0.98  --dbg_backtrace                         false
% 1.96/0.98  --dbg_dump_prop_clauses                 false
% 1.96/0.98  --dbg_dump_prop_clauses_file            -
% 1.96/0.98  --dbg_out_stat                          false
% 1.96/0.98  ------ Parsing...
% 1.96/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/0.98  ------ Proving...
% 1.96/0.98  ------ Problem Properties 
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  clauses                                 11
% 1.96/0.98  conjectures                             1
% 1.96/0.98  EPR                                     0
% 1.96/0.98  Horn                                    11
% 1.96/0.98  unary                                   6
% 1.96/0.98  binary                                  3
% 1.96/0.98  lits                                    21
% 1.96/0.98  lits eq                                 11
% 1.96/0.98  fd_pure                                 0
% 1.96/0.98  fd_pseudo                               0
% 1.96/0.98  fd_cond                                 0
% 1.96/0.98  fd_pseudo_cond                          0
% 1.96/0.98  AC symbols                              0
% 1.96/0.98  
% 1.96/0.98  ------ Schedule dynamic 5 is on 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  ------ 
% 1.96/0.98  Current options:
% 1.96/0.98  ------ 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options
% 1.96/0.98  
% 1.96/0.98  --out_options                           all
% 1.96/0.98  --tptp_safe_out                         true
% 1.96/0.98  --problem_path                          ""
% 1.96/0.98  --include_path                          ""
% 1.96/0.98  --clausifier                            res/vclausify_rel
% 1.96/0.98  --clausifier_options                    --mode clausify
% 1.96/0.98  --stdin                                 false
% 1.96/0.98  --stats_out                             all
% 1.96/0.98  
% 1.96/0.98  ------ General Options
% 1.96/0.98  
% 1.96/0.98  --fof                                   false
% 1.96/0.98  --time_out_real                         305.
% 1.96/0.98  --time_out_virtual                      -1.
% 1.96/0.98  --symbol_type_check                     false
% 1.96/0.98  --clausify_out                          false
% 1.96/0.98  --sig_cnt_out                           false
% 1.96/0.98  --trig_cnt_out                          false
% 1.96/0.98  --trig_cnt_out_tolerance                1.
% 1.96/0.98  --trig_cnt_out_sk_spl                   false
% 1.96/0.98  --abstr_cl_out                          false
% 1.96/0.98  
% 1.96/0.98  ------ Global Options
% 1.96/0.98  
% 1.96/0.98  --schedule                              default
% 1.96/0.98  --add_important_lit                     false
% 1.96/0.98  --prop_solver_per_cl                    1000
% 1.96/0.98  --min_unsat_core                        false
% 1.96/0.98  --soft_assumptions                      false
% 1.96/0.98  --soft_lemma_size                       3
% 1.96/0.98  --prop_impl_unit_size                   0
% 1.96/0.98  --prop_impl_unit                        []
% 1.96/0.98  --share_sel_clauses                     true
% 1.96/0.98  --reset_solvers                         false
% 1.96/0.98  --bc_imp_inh                            [conj_cone]
% 1.96/0.98  --conj_cone_tolerance                   3.
% 1.96/0.98  --extra_neg_conj                        none
% 1.96/0.98  --large_theory_mode                     true
% 1.96/0.98  --prolific_symb_bound                   200
% 1.96/0.98  --lt_threshold                          2000
% 1.96/0.98  --clause_weak_htbl                      true
% 1.96/0.98  --gc_record_bc_elim                     false
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing Options
% 1.96/0.98  
% 1.96/0.98  --preprocessing_flag                    true
% 1.96/0.98  --time_out_prep_mult                    0.1
% 1.96/0.98  --splitting_mode                        input
% 1.96/0.98  --splitting_grd                         true
% 1.96/0.98  --splitting_cvd                         false
% 1.96/0.98  --splitting_cvd_svl                     false
% 1.96/0.98  --splitting_nvd                         32
% 1.96/0.98  --sub_typing                            true
% 1.96/0.98  --prep_gs_sim                           true
% 1.96/0.98  --prep_unflatten                        true
% 1.96/0.98  --prep_res_sim                          true
% 1.96/0.98  --prep_upred                            true
% 1.96/0.98  --prep_sem_filter                       exhaustive
% 1.96/0.98  --prep_sem_filter_out                   false
% 1.96/0.98  --pred_elim                             true
% 1.96/0.98  --res_sim_input                         true
% 1.96/0.98  --eq_ax_congr_red                       true
% 1.96/0.98  --pure_diseq_elim                       true
% 1.96/0.98  --brand_transform                       false
% 1.96/0.98  --non_eq_to_eq                          false
% 1.96/0.98  --prep_def_merge                        true
% 1.96/0.98  --prep_def_merge_prop_impl              false
% 1.96/0.98  --prep_def_merge_mbd                    true
% 1.96/0.98  --prep_def_merge_tr_red                 false
% 1.96/0.98  --prep_def_merge_tr_cl                  false
% 1.96/0.98  --smt_preprocessing                     true
% 1.96/0.98  --smt_ac_axioms                         fast
% 1.96/0.98  --preprocessed_out                      false
% 1.96/0.98  --preprocessed_stats                    false
% 1.96/0.98  
% 1.96/0.98  ------ Abstraction refinement Options
% 1.96/0.98  
% 1.96/0.98  --abstr_ref                             []
% 1.96/0.98  --abstr_ref_prep                        false
% 1.96/0.98  --abstr_ref_until_sat                   false
% 1.96/0.98  --abstr_ref_sig_restrict                funpre
% 1.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.98  --abstr_ref_under                       []
% 1.96/0.98  
% 1.96/0.98  ------ SAT Options
% 1.96/0.98  
% 1.96/0.98  --sat_mode                              false
% 1.96/0.98  --sat_fm_restart_options                ""
% 1.96/0.98  --sat_gr_def                            false
% 1.96/0.98  --sat_epr_types                         true
% 1.96/0.98  --sat_non_cyclic_types                  false
% 1.96/0.98  --sat_finite_models                     false
% 1.96/0.98  --sat_fm_lemmas                         false
% 1.96/0.98  --sat_fm_prep                           false
% 1.96/0.98  --sat_fm_uc_incr                        true
% 1.96/0.98  --sat_out_model                         small
% 1.96/0.98  --sat_out_clauses                       false
% 1.96/0.98  
% 1.96/0.98  ------ QBF Options
% 1.96/0.98  
% 1.96/0.98  --qbf_mode                              false
% 1.96/0.98  --qbf_elim_univ                         false
% 1.96/0.98  --qbf_dom_inst                          none
% 1.96/0.98  --qbf_dom_pre_inst                      false
% 1.96/0.98  --qbf_sk_in                             false
% 1.96/0.98  --qbf_pred_elim                         true
% 1.96/0.98  --qbf_split                             512
% 1.96/0.98  
% 1.96/0.98  ------ BMC1 Options
% 1.96/0.98  
% 1.96/0.98  --bmc1_incremental                      false
% 1.96/0.98  --bmc1_axioms                           reachable_all
% 1.96/0.98  --bmc1_min_bound                        0
% 1.96/0.98  --bmc1_max_bound                        -1
% 1.96/0.98  --bmc1_max_bound_default                -1
% 1.96/0.98  --bmc1_symbol_reachability              true
% 1.96/0.98  --bmc1_property_lemmas                  false
% 1.96/0.98  --bmc1_k_induction                      false
% 1.96/0.98  --bmc1_non_equiv_states                 false
% 1.96/0.98  --bmc1_deadlock                         false
% 1.96/0.98  --bmc1_ucm                              false
% 1.96/0.98  --bmc1_add_unsat_core                   none
% 1.96/0.98  --bmc1_unsat_core_children              false
% 1.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.98  --bmc1_out_stat                         full
% 1.96/0.98  --bmc1_ground_init                      false
% 1.96/0.98  --bmc1_pre_inst_next_state              false
% 1.96/0.98  --bmc1_pre_inst_state                   false
% 1.96/0.98  --bmc1_pre_inst_reach_state             false
% 1.96/0.98  --bmc1_out_unsat_core                   false
% 1.96/0.98  --bmc1_aig_witness_out                  false
% 1.96/0.98  --bmc1_verbose                          false
% 1.96/0.98  --bmc1_dump_clauses_tptp                false
% 1.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.98  --bmc1_dump_file                        -
% 1.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.98  --bmc1_ucm_extend_mode                  1
% 1.96/0.98  --bmc1_ucm_init_mode                    2
% 1.96/0.98  --bmc1_ucm_cone_mode                    none
% 1.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.98  --bmc1_ucm_relax_model                  4
% 1.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.98  --bmc1_ucm_layered_model                none
% 1.96/0.98  --bmc1_ucm_max_lemma_size               10
% 1.96/0.98  
% 1.96/0.98  ------ AIG Options
% 1.96/0.98  
% 1.96/0.98  --aig_mode                              false
% 1.96/0.98  
% 1.96/0.98  ------ Instantiation Options
% 1.96/0.98  
% 1.96/0.98  --instantiation_flag                    true
% 1.96/0.98  --inst_sos_flag                         false
% 1.96/0.98  --inst_sos_phase                        true
% 1.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel_side                     none
% 1.96/0.98  --inst_solver_per_active                1400
% 1.96/0.98  --inst_solver_calls_frac                1.
% 1.96/0.98  --inst_passive_queue_type               priority_queues
% 1.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.98  --inst_passive_queues_freq              [25;2]
% 1.96/0.98  --inst_dismatching                      true
% 1.96/0.98  --inst_eager_unprocessed_to_passive     true
% 1.96/0.98  --inst_prop_sim_given                   true
% 1.96/0.98  --inst_prop_sim_new                     false
% 1.96/0.98  --inst_subs_new                         false
% 1.96/0.98  --inst_eq_res_simp                      false
% 1.96/0.98  --inst_subs_given                       false
% 1.96/0.98  --inst_orphan_elimination               true
% 1.96/0.98  --inst_learning_loop_flag               true
% 1.96/0.98  --inst_learning_start                   3000
% 1.96/0.98  --inst_learning_factor                  2
% 1.96/0.98  --inst_start_prop_sim_after_learn       3
% 1.96/0.98  --inst_sel_renew                        solver
% 1.96/0.98  --inst_lit_activity_flag                true
% 1.96/0.98  --inst_restr_to_given                   false
% 1.96/0.98  --inst_activity_threshold               500
% 1.96/0.98  --inst_out_proof                        true
% 1.96/0.98  
% 1.96/0.98  ------ Resolution Options
% 1.96/0.98  
% 1.96/0.98  --resolution_flag                       false
% 1.96/0.98  --res_lit_sel                           adaptive
% 1.96/0.98  --res_lit_sel_side                      none
% 1.96/0.98  --res_ordering                          kbo
% 1.96/0.98  --res_to_prop_solver                    active
% 1.96/0.98  --res_prop_simpl_new                    false
% 1.96/0.98  --res_prop_simpl_given                  true
% 1.96/0.98  --res_passive_queue_type                priority_queues
% 1.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.98  --res_passive_queues_freq               [15;5]
% 1.96/0.98  --res_forward_subs                      full
% 1.96/0.98  --res_backward_subs                     full
% 1.96/0.98  --res_forward_subs_resolution           true
% 1.96/0.98  --res_backward_subs_resolution          true
% 1.96/0.98  --res_orphan_elimination                true
% 1.96/0.98  --res_time_limit                        2.
% 1.96/0.98  --res_out_proof                         true
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Options
% 1.96/0.98  
% 1.96/0.98  --superposition_flag                    true
% 1.96/0.98  --sup_passive_queue_type                priority_queues
% 1.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.98  --demod_completeness_check              fast
% 1.96/0.98  --demod_use_ground                      true
% 1.96/0.98  --sup_to_prop_solver                    passive
% 1.96/0.98  --sup_prop_simpl_new                    true
% 1.96/0.98  --sup_prop_simpl_given                  true
% 1.96/0.98  --sup_fun_splitting                     false
% 1.96/0.98  --sup_smt_interval                      50000
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Simplification Setup
% 1.96/0.98  
% 1.96/0.98  --sup_indices_passive                   []
% 1.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_full_bw                           [BwDemod]
% 1.96/0.98  --sup_immed_triv                        [TrivRules]
% 1.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_immed_bw_main                     []
% 1.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  
% 1.96/0.98  ------ Combination Options
% 1.96/0.98  
% 1.96/0.98  --comb_res_mult                         3
% 1.96/0.98  --comb_sup_mult                         2
% 1.96/0.98  --comb_inst_mult                        10
% 1.96/0.98  
% 1.96/0.98  ------ Debug Options
% 1.96/0.98  
% 1.96/0.98  --dbg_backtrace                         false
% 1.96/0.98  --dbg_dump_prop_clauses                 false
% 1.96/0.98  --dbg_dump_prop_clauses_file            -
% 1.96/0.98  --dbg_out_stat                          false
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  ------ Proving...
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  % SZS output start Saturation for theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  fof(f13,axiom,(
% 1.96/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f39,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/0.98    inference(ennf_transformation,[],[f13])).
% 1.96/0.98  
% 1.96/0.98  fof(f87,plain,(
% 1.96/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f39])).
% 1.96/0.98  
% 1.96/0.98  fof(f15,conjecture,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f16,negated_conjecture,(
% 1.96/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 1.96/0.98    inference(negated_conjecture,[],[f15])).
% 1.96/0.98  
% 1.96/0.98  fof(f42,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f16])).
% 1.96/0.98  
% 1.96/0.98  fof(f43,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f42])).
% 1.96/0.98  
% 1.96/0.98  fof(f60,plain,(
% 1.96/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK5) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f59,plain,(
% 1.96/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK4,k8_tmap_1(X0,sK4),k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),sK4),X2) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f58,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK3,X1),k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f61,plain,(
% 1.96/0.98    ((~r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5) & m1_subset_1(sK5,u1_struct_0(sK4))) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f60,f59,f58])).
% 1.96/0.98  
% 1.96/0.98  fof(f100,plain,(
% 1.96/0.98    m1_pre_topc(sK4,sK3)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f98,plain,(
% 1.96/0.98    l1_pre_topc(sK3)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f6,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f25,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f6])).
% 1.96/0.98  
% 1.96/0.98  fof(f26,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f25])).
% 1.96/0.98  
% 1.96/0.98  fof(f68,plain,(
% 1.96/0.98    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f26])).
% 1.96/0.98  
% 1.96/0.98  fof(f97,plain,(
% 1.96/0.98    v2_pre_topc(sK3)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f96,plain,(
% 1.96/0.98    ~v2_struct_0(sK3)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f11,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f35,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f11])).
% 1.96/0.98  
% 1.96/0.98  fof(f36,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f35])).
% 1.96/0.98  
% 1.96/0.98  fof(f84,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f36])).
% 1.96/0.98  
% 1.96/0.98  fof(f107,plain,(
% 1.96/0.98    ( ! [X2,X0] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f84])).
% 1.96/0.98  
% 1.96/0.98  fof(f44,plain,(
% 1.96/0.98    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))),
% 1.96/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.96/0.98  
% 1.96/0.98  fof(f51,plain,(
% 1.96/0.98    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X0,X2)))),
% 1.96/0.98    inference(nnf_transformation,[],[f44])).
% 1.96/0.98  
% 1.96/0.98  fof(f52,plain,(
% 1.96/0.98    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X0,X2)))),
% 1.96/0.98    inference(flattening,[],[f51])).
% 1.96/0.98  
% 1.96/0.98  fof(f53,plain,(
% 1.96/0.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) & ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X2,X1,X0) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) | ~sP0(X0,X1,X2)))),
% 1.96/0.98    inference(rectify,[],[f52])).
% 1.96/0.98  
% 1.96/0.98  fof(f92,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X1,X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f53])).
% 1.96/0.98  
% 1.96/0.98  fof(f83,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f36])).
% 1.96/0.98  
% 1.96/0.98  fof(f108,plain,(
% 1.96/0.98    ( ! [X2,X0] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f83])).
% 1.96/0.98  
% 1.96/0.98  fof(f85,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f36])).
% 1.96/0.98  
% 1.96/0.98  fof(f106,plain,(
% 1.96/0.98    ( ! [X2,X0] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f85])).
% 1.96/0.98  
% 1.96/0.98  fof(f82,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f36])).
% 1.96/0.98  
% 1.96/0.98  fof(f109,plain,(
% 1.96/0.98    ( ! [X2,X0] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f82])).
% 1.96/0.98  
% 1.96/0.98  fof(f14,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => r1_tmap_1(X0,X1,X2,X3))))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f40,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> ! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f14])).
% 1.96/0.98  
% 1.96/0.98  fof(f41,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> ! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f40])).
% 1.96/0.98  
% 1.96/0.98  fof(f45,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((sP0(X1,X0,X2) <=> ! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(definition_folding,[],[f41,f44])).
% 1.96/0.98  
% 1.96/0.98  fof(f54,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((sP0(X1,X0,X2) | ? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(nnf_transformation,[],[f45])).
% 1.96/0.98  
% 1.96/0.98  fof(f55,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((sP0(X1,X0,X2) | ? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X1,X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(rectify,[],[f54])).
% 1.96/0.98  
% 1.96/0.98  fof(f56,plain,(
% 1.96/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_tmap_1(X0,X1,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f57,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((sP0(X1,X0,X2) | (~r1_tmap_1(X0,X1,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X1,X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).
% 1.96/0.98  
% 1.96/0.98  fof(f93,plain,(
% 1.96/0.98    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~sP0(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f57])).
% 1.96/0.98  
% 1.96/0.98  fof(f102,plain,(
% 1.96/0.98    ~r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f99,plain,(
% 1.96/0.98    ~v2_struct_0(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f101,plain,(
% 1.96/0.98    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.96/0.98    inference(cnf_transformation,[],[f61])).
% 1.96/0.98  
% 1.96/0.98  fof(f88,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~sP0(X0,X1,X2)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f53])).
% 1.96/0.98  
% 1.96/0.98  fof(f91,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f53])).
% 1.96/0.98  
% 1.96/0.98  fof(f89,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f53])).
% 1.96/0.98  
% 1.96/0.98  fof(f1,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f17,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f1])).
% 1.96/0.98  
% 1.96/0.98  fof(f18,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.98    inference(flattening,[],[f17])).
% 1.96/0.98  
% 1.96/0.98  fof(f62,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f18])).
% 1.96/0.98  
% 1.96/0.98  fof(f3,axiom,(
% 1.96/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f20,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/0.98    inference(ennf_transformation,[],[f3])).
% 1.96/0.98  
% 1.96/0.98  fof(f64,plain,(
% 1.96/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f20])).
% 1.96/0.98  
% 1.96/0.98  fof(f7,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f27,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f7])).
% 1.96/0.98  
% 1.96/0.98  fof(f28,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f27])).
% 1.96/0.98  
% 1.96/0.98  fof(f47,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(nnf_transformation,[],[f28])).
% 1.96/0.98  
% 1.96/0.98  fof(f48,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(rectify,[],[f47])).
% 1.96/0.98  
% 1.96/0.98  fof(f49,plain,(
% 1.96/0.98    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f50,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 1.96/0.98  
% 1.96/0.98  fof(f69,plain,(
% 1.96/0.98    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f50])).
% 1.96/0.98  
% 1.96/0.98  fof(f104,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f69])).
% 1.96/0.98  
% 1.96/0.98  fof(f105,plain,(
% 1.96/0.98    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f104])).
% 1.96/0.98  
% 1.96/0.98  fof(f10,axiom,(
% 1.96/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f33,plain,(
% 1.96/0.98    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f10])).
% 1.96/0.98  
% 1.96/0.98  fof(f34,plain,(
% 1.96/0.98    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f33])).
% 1.96/0.98  
% 1.96/0.98  fof(f80,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f34])).
% 1.96/0.98  
% 1.96/0.98  fof(f81,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f34])).
% 1.96/0.98  
% 1.96/0.98  fof(f8,axiom,(
% 1.96/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f29,plain,(
% 1.96/0.98    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f8])).
% 1.96/0.98  
% 1.96/0.98  fof(f30,plain,(
% 1.96/0.98    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f29])).
% 1.96/0.98  
% 1.96/0.98  fof(f75,plain,(
% 1.96/0.98    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f30])).
% 1.96/0.98  
% 1.96/0.98  fof(f79,plain,(
% 1.96/0.98    ( ! [X0,X1] : (~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f34])).
% 1.96/0.98  
% 1.96/0.98  fof(f74,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f30])).
% 1.96/0.98  
% 1.96/0.98  fof(f2,axiom,(
% 1.96/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f19,plain,(
% 1.96/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.96/0.98    inference(ennf_transformation,[],[f2])).
% 1.96/0.98  
% 1.96/0.98  fof(f63,plain,(
% 1.96/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f19])).
% 1.96/0.98  
% 1.96/0.98  fof(f4,axiom,(
% 1.96/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f21,plain,(
% 1.96/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f4])).
% 1.96/0.98  
% 1.96/0.98  fof(f22,plain,(
% 1.96/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f21])).
% 1.96/0.98  
% 1.96/0.98  fof(f65,plain,(
% 1.96/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f22])).
% 1.96/0.98  
% 1.96/0.98  fof(f5,axiom,(
% 1.96/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f23,plain,(
% 1.96/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.96/0.98    inference(ennf_transformation,[],[f5])).
% 1.96/0.98  
% 1.96/0.98  fof(f24,plain,(
% 1.96/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.96/0.98    inference(flattening,[],[f23])).
% 1.96/0.98  
% 1.96/0.98  fof(f46,plain,(
% 1.96/0.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.96/0.98    inference(nnf_transformation,[],[f24])).
% 1.96/0.98  
% 1.96/0.98  fof(f66,plain,(
% 1.96/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f46])).
% 1.96/0.98  
% 1.96/0.98  fof(f12,axiom,(
% 1.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f37,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f12])).
% 1.96/0.98  
% 1.96/0.98  fof(f38,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f37])).
% 1.96/0.98  
% 1.96/0.98  fof(f86,plain,(
% 1.96/0.98    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f9,axiom,(
% 1.96/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f31,plain,(
% 1.96/0.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f9])).
% 1.96/0.98  
% 1.96/0.98  fof(f32,plain,(
% 1.96/0.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f31])).
% 1.96/0.98  
% 1.96/0.98  fof(f77,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f32])).
% 1.96/0.98  
% 1.96/0.98  fof(f78,plain,(
% 1.96/0.98    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f32])).
% 1.96/0.98  
% 1.96/0.98  fof(f76,plain,(
% 1.96/0.98    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f32])).
% 1.96/0.98  
% 1.96/0.98  fof(f94,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f57])).
% 1.96/0.98  
% 1.96/0.98  cnf(c_422,plain,
% 1.96/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/0.98      | r1_tmap_1(X4,X5,X6,X7)
% 1.96/0.98      | X6 != X2
% 1.96/0.98      | X4 != X0
% 1.96/0.98      | X5 != X1
% 1.96/0.98      | X7 != X3 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_421,plain,
% 1.96/0.98      ( ~ v5_pre_topc(X0,X1,X2) | v5_pre_topc(X3,X1,X4) | X3 != X0 | X4 != X2 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_418,plain,
% 1.96/0.98      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_413,plain,
% 1.96/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_412,plain,
% 1.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/0.98      | v1_funct_2(X3,X4,X5)
% 1.96/0.98      | X5 != X2
% 1.96/0.98      | X3 != X0
% 1.96/0.98      | X4 != X1 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_408,plain,
% 1.96/0.98      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.96/0.98      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 1.96/0.98      | X8 != X2
% 1.96/0.98      | X6 != X0
% 1.96/0.98      | X7 != X1
% 1.96/0.98      | X9 != X3
% 1.96/0.98      | X10 != X4
% 1.96/0.98      | X11 != X5 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_407,plain,
% 1.96/0.98      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_406,plain,
% 1.96/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_404,plain,
% 1.96/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_403,plain,
% 1.96/0.98      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_402,plain,
% 1.96/0.98      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 1.96/0.98      theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2106,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_25,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.98      | ~ m1_pre_topc(X0,X1)
% 1.96/0.98      | ~ l1_pre_topc(X1) ),
% 1.96/0.98      inference(cnf_transformation,[],[f87]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_36,negated_conjecture,
% 1.96/0.98      ( m1_pre_topc(sK4,sK3) ),
% 1.96/0.98      inference(cnf_transformation,[],[f100]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1410,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.98      | ~ l1_pre_topc(X1)
% 1.96/0.98      | sK3 != X1
% 1.96/0.98      | sK4 != X0 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1411,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/0.98      | ~ l1_pre_topc(sK3) ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_1410]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_38,negated_conjecture,
% 1.96/0.98      ( l1_pre_topc(sK3) ),
% 1.96/0.98      inference(cnf_transformation,[],[f98]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1413,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.96/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1411,c_38]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2103,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.96/0.98      inference(subtyping,[status(esa)],[c_1413]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2290,plain,
% 1.96/0.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_6,plain,
% 1.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ l1_pre_topc(X1)
% 1.96/0.98      | ~ v2_pre_topc(X1)
% 1.96/0.98      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 1.96/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_39,negated_conjecture,
% 1.96/0.98      ( v2_pre_topc(sK3) ),
% 1.96/0.98      inference(cnf_transformation,[],[f97]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1756,plain,
% 1.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ l1_pre_topc(X1)
% 1.96/0.98      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 1.96/0.98      | sK3 != X1 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_39]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1757,plain,
% 1.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/0.98      | v2_struct_0(sK3)
% 1.96/0.98      | ~ l1_pre_topc(sK3)
% 1.96/0.98      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_1756]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_40,negated_conjecture,
% 1.96/0.98      ( ~ v2_struct_0(sK3) ),
% 1.96/0.98      inference(cnf_transformation,[],[f96]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_1761,plain,
% 1.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/0.98      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_1757,c_40,c_38]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2099,plain,
% 1.96/0.98      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/0.98      | k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3)) ),
% 1.96/0.98      inference(subtyping,[status(esa)],[c_1761]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2293,plain,
% 1.96/0.98      ( k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3))
% 1.96/0.98      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_2099]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2413,plain,
% 1.96/0.98      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 1.96/0.98      inference(superposition,[status(thm)],[c_2290,c_2293]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_21,plain,
% 1.96/0.98      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),X1,k6_tmap_1(X0,u1_struct_0(X1)))
% 1.96/0.98      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ m1_pre_topc(X1,X0)
% 1.96/0.98      | v2_struct_0(X0)
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ l1_pre_topc(X0)
% 1.96/0.98      | ~ v2_pre_topc(X0) ),
% 1.96/0.98      inference(cnf_transformation,[],[f107]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_26,plain,
% 1.96/0.98      ( sP0(X0,X1,X2)
% 1.96/0.98      | ~ v5_pre_topc(X2,X1,X0)
% 1.96/0.98      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
% 1.96/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.96/0.99      | ~ v1_funct_1(X2) ),
% 1.96/0.99      inference(cnf_transformation,[],[f92]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_481,plain,
% 1.96/0.99      ( sP0(X0,X1,X2)
% 1.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.96/0.99      | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X4)))
% 1.96/0.99      | ~ m1_pre_topc(X3,X4)
% 1.96/0.99      | ~ v1_funct_1(X2)
% 1.96/0.99      | v2_struct_0(X3)
% 1.96/0.99      | v2_struct_0(X4)
% 1.96/0.99      | ~ l1_pre_topc(X4)
% 1.96/0.99      | ~ v2_pre_topc(X4)
% 1.96/0.99      | X1 != X3
% 1.96/0.99      | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X2
% 1.96/0.99      | k6_tmap_1(X4,u1_struct_0(X3)) != X0 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_482,plain,
% 1.96/0.99      ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 1.96/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_22,plain,
% 1.96/0.99      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 1.96/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f108]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_20,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 1.96/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f106]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_486,plain,
% 1.96/0.99      ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_482,c_22,c_20]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_23,plain,
% 1.96/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.99      | ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f109]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_242,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_23,c_25]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_508,plain,
% 1.96/0.99      ( sP0(k6_tmap_1(X0,u1_struct_0(X1)),X1,k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(forward_subsumption_resolution,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_486,c_242,c_25]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_33,plain,
% 1.96/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.96/0.99      | ~ sP0(X1,X0,X2)
% 1.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/0.99      | ~ v1_funct_1(X2)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f93]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_34,negated_conjecture,
% 1.96/0.99      ( ~ r1_tmap_1(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),sK5) ),
% 1.96/0.99      inference(cnf_transformation,[],[f102]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_628,plain,
% 1.96/0.99      ( ~ sP0(X0,X1,X2)
% 1.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.96/0.99      | ~ v1_funct_1(X2)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != X2
% 1.96/0.99      | k8_tmap_1(sK3,sK4) != X0
% 1.96/0.99      | sK5 != X3
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_34]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_629,plain,
% 1.96/0.99      ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_628]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_37,negated_conjecture,
% 1.96/0.99      ( ~ v2_struct_0(sK4) ),
% 1.96/0.99      inference(cnf_transformation,[],[f99]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_35,negated_conjecture,
% 1.96/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.96/0.99      inference(cnf_transformation,[],[f101]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_631,plain,
% 1.96/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_629,c_37,c_35]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_632,plain,
% 1.96/0.99      ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_631]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_30,plain,
% 1.96/0.99      ( ~ sP0(X0,X1,X2) | v1_funct_1(X2) ),
% 1.96/0.99      inference(cnf_transformation,[],[f88]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_27,plain,
% 1.96/0.99      ( ~ sP0(X0,X1,X2)
% 1.96/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 1.96/0.99      inference(cnf_transformation,[],[f91]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_29,plain,
% 1.96/0.99      ( ~ sP0(X0,X1,X2) | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) ),
% 1.96/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_653,plain,
% 1.96/0.99      ( ~ sP0(k8_tmap_1(sK3,sK4),sK4,k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(forward_subsumption_resolution,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_632,c_30,c_27,c_29]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_915,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4)
% 1.96/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
% 1.96/0.99      | sK4 != X0 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_508,c_653]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_916,plain,
% 1.96/0.99      ( ~ m1_pre_topc(sK4,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4)
% 1.96/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_915]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_920,plain,
% 1.96/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ m1_pre_topc(sK4,X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4)
% 1.96/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_916,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_921,plain,
% 1.96/0.99      ( ~ m1_pre_topc(sK4,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4)
% 1.96/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_920]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_0,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_948,plain,
% 1.96/0.99      ( ~ m1_pre_topc(sK4,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_921,c_0,c_2]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1646,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK4)),k7_tmap_1(X0,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != sK4 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_948]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1647,plain,
% 1.96/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK3)
% 1.96/0.99      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1646]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_959,plain,
% 1.96/0.99      ( ~ m1_pre_topc(sK4,sK3)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK3)
% 1.96/0.99      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)
% 1.96/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(instantiation,[status(thm)],[c_948]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_10,plain,
% 1.96/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.99      | ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 1.96/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f105]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_18,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_17,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | v2_pre_topc(k8_tmap_1(X1,X0)) ),
% 1.96/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_11,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | l1_pre_topc(k8_tmap_1(X1,X0))
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_261,plain,
% 1.96/0.99      ( ~ v2_pre_topc(X1)
% 1.96/0.99      | ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_10,c_25,c_18,c_17,c_11]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_262,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_261]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1391,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_262,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1392,plain,
% 1.96/0.99      ( v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3)
% 1.96/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1391]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_19,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ v2_struct_0(k8_tmap_1(X1,X0))
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1421,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | ~ v2_struct_0(k8_tmap_1(X0,X1))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1422,plain,
% 1.96/0.99      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1421]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_12,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | v2_pre_topc(k8_tmap_1(X1,X0)) ),
% 1.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1454,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | v2_pre_topc(k8_tmap_1(X0,X1))
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1455,plain,
% 1.96/0.99      ( v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1454]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1465,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1466,plain,
% 1.96/0.99      ( v2_struct_0(sK3)
% 1.96/0.99      | l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1465]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1649,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1647,c_40,c_39,c_38,c_36,c_959,c_1392,c_1422,c_1455,c_1466]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2100,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1649]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1394,plain,
% 1.96/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1392,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2104,plain,
% 1.96/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1394]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2314,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 1.96/0.99      inference(light_normalisation,[status(thm)],[c_2100,c_2104]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2607,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) ),
% 1.96/0.99      inference(demodulation,[status(thm)],[c_2413,c_2314]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_856,plain,
% 1.96/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.96/0.99      | ~ m1_pre_topc(X3,X4)
% 1.96/0.99      | v2_struct_0(X4)
% 1.96/0.99      | v2_struct_0(X3)
% 1.96/0.99      | ~ l1_pre_topc(X4)
% 1.96/0.99      | ~ v2_pre_topc(X4)
% 1.96/0.99      | X3 != X1
% 1.96/0.99      | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X0
% 1.96/0.99      | k6_tmap_1(X4,u1_struct_0(X3)) != X2 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_508]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_857,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_856]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1552,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_857,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1553,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1552]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1555,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1553,c_40,c_39,c_38,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2102,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1555]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2291,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2321,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 1.96/0.99      inference(light_normalisation,[status(thm)],[c_2291,c_2104]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2606,plain,
% 1.96/0.99      ( m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 1.96/0.99      inference(demodulation,[status(thm)],[c_2413,c_2321]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1,plain,
% 1.96/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_3,plain,
% 1.96/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_462,plain,
% 1.96/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 1.96/0.99      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_5,plain,
% 1.96/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.96/0.99      | ~ v1_funct_2(X5,X2,X3)
% 1.96/0.99      | ~ v1_funct_2(X4,X0,X1)
% 1.96/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.96/0.99      | ~ v1_funct_1(X5)
% 1.96/0.99      | ~ v1_funct_1(X4)
% 1.96/0.99      | v1_xboole_0(X1)
% 1.96/0.99      | v1_xboole_0(X3)
% 1.96/0.99      | X4 = X5 ),
% 1.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_24,plain,
% 1.96/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_527,plain,
% 1.96/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/0.99      | ~ v1_funct_2(X3,X4,X5)
% 1.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.96/0.99      | ~ m1_pre_topc(X6,X7)
% 1.96/0.99      | ~ v1_funct_1(X0)
% 1.96/0.99      | ~ v1_funct_1(X3)
% 1.96/0.99      | v2_struct_0(X7)
% 1.96/0.99      | v2_struct_0(X6)
% 1.96/0.99      | v1_xboole_0(X5)
% 1.96/0.99      | v1_xboole_0(X2)
% 1.96/0.99      | ~ l1_pre_topc(X7)
% 1.96/0.99      | ~ v2_pre_topc(X7)
% 1.96/0.99      | X3 = X0
% 1.96/0.99      | k9_tmap_1(X7,X6) != X0
% 1.96/0.99      | k3_struct_0(X7) != X3
% 1.96/0.99      | u1_struct_0(X7) != X5
% 1.96/0.99      | u1_struct_0(X7) != X4
% 1.96/0.99      | u1_struct_0(X7) != X1
% 1.96/0.99      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_528,plain,
% 1.96/0.99      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v1_xboole_0(u1_struct_0(X0))
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_527]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_15,plain,
% 1.96/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_14,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_532,plain,
% 1.96/0.99      ( v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.96/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.96/0.99      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_528,c_15,c_14,c_462]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_533,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_532]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_16,plain,
% 1.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.96/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X1) ),
% 1.96/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_560,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 1.96/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_533,c_16]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1574,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(X0))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_560,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1575,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1574]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1577,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1575,c_40,c_39,c_38,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1716,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(X0) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_462,c_1577]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1468,plain,
% 1.96/0.99      ( l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1466,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1842,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | k8_tmap_1(sK3,sK4) != X0
% 1.96/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(X0) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_1716,c_1468]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1843,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1842]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1845,plain,
% 1.96/0.99      ( ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1843,c_40,c_39,c_38,c_1422]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1846,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | ~ v1_funct_1(k3_struct_0(sK3))
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_1845]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1399,plain,
% 1.96/0.99      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_242,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1400,plain,
% 1.96/0.99      ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1399]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1402,plain,
% 1.96/0.99      ( v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1400,c_40,c_39,c_38,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1930,plain,
% 1.96/0.99      ( ~ v1_funct_2(k3_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
% 1.96/0.99      | ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_1846,c_1402]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_832,plain,
% 1.96/0.99      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.96/0.99      | ~ m1_pre_topc(X3,X4)
% 1.96/0.99      | v2_struct_0(X4)
% 1.96/0.99      | v2_struct_0(X3)
% 1.96/0.99      | ~ l1_pre_topc(X4)
% 1.96/0.99      | ~ v2_pre_topc(X4)
% 1.96/0.99      | X3 != X1
% 1.96/0.99      | k2_tmap_1(X4,k6_tmap_1(X4,u1_struct_0(X3)),k7_tmap_1(X4,u1_struct_0(X3)),X3) != X0
% 1.96/0.99      | k6_tmap_1(X4,u1_struct_0(X3)) != X2 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_508]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_833,plain,
% 1.96/0.99      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 1.96/0.99      | ~ m1_pre_topc(X1,X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_832]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1563,plain,
% 1.96/0.99      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X1)),k7_tmap_1(X0,u1_struct_0(X1)),X1),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_833,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1564,plain,
% 1.96/0.99      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1563]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1566,plain,
% 1.96/0.99      ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1564,c_40,c_39,c_38,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1972,plain,
% 1.96/0.99      ( ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_1930,c_1566]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2096,plain,
% 1.96/0.99      ( ~ m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.96/0.99      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1972]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2296,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4)
% 1.96/0.99      | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2324,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4)
% 1.96/0.99      | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 1.96/0.99      inference(light_normalisation,[status(thm)],[c_2296,c_2104]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2605,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK4) != k3_struct_0(sK3)
% 1.96/0.99      | k9_tmap_1(sK3,sK4) = k3_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4)
% 1.96/0.99      | m1_subset_1(k3_struct_0(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 1.96/0.99      inference(demodulation,[status(thm)],[c_2413,c_2324]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1541,plain,
% 1.96/0.99      ( ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | v2_pre_topc(X1)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1542,plain,
% 1.96/0.99      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | v2_pre_topc(sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1541]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1544,plain,
% 1.96/0.99      ( v2_pre_topc(sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1542,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1530,plain,
% 1.96/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1531,plain,
% 1.96/0.99      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1530]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1533,plain,
% 1.96/0.99      ( l1_pre_topc(sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1531,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1457,plain,
% 1.96/0.99      ( v2_pre_topc(k8_tmap_1(sK3,sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1455,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1424,plain,
% 1.96/0.99      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1422,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_32,plain,
% 1.96/0.99      ( sP0(X0,X1,X2)
% 1.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
% 1.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.96/0.99      | m1_subset_1(sK2(X1,X0,X2),u1_struct_0(X1))
% 1.96/0.99      | ~ v1_funct_1(X2)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X0) ),
% 1.96/0.99      inference(cnf_transformation,[],[f94]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_880,plain,
% 1.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.96/0.99      | m1_subset_1(sK2(X1,X2,X0),u1_struct_0(X1))
% 1.96/0.99      | ~ v1_funct_1(X0)
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | v2_struct_0(X2)
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | ~ l1_pre_topc(X2)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(X1)
% 1.96/0.99      | ~ v2_pre_topc(X2)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4)
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != X0
% 1.96/0.99      | k8_tmap_1(sK3,sK4) != X2
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_653]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_881,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_880]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_883,plain,
% 1.96/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_881,c_37]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_884,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(renaming,[status(thm)],[c_883]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1660,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1424,c_884]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1668,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1457,c_1660]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1672,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1468,c_1668]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1688,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4))
% 1.96/0.99      | ~ v2_pre_topc(sK4) ),
% 1.96/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1672]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1692,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)) ),
% 1.96/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1544,c_1688]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1432,plain,
% 1.96/0.99      ( v1_funct_1(k9_tmap_1(X0,X1))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1433,plain,
% 1.96/0.99      ( v1_funct_1(k9_tmap_1(sK3,sK4))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1432]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1435,plain,
% 1.96/0.99      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1433,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1947,plain,
% 1.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_1692,c_1435]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1597,plain,
% 1.96/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1598,plain,
% 1.96/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1597]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1600,plain,
% 1.96/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1598,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1992,plain,
% 1.96/0.99      ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
% 1.96/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_1947,c_1600]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2031,plain,
% 1.96/0.99      ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 1.96/0.99      inference(equality_resolution_simp,[status(thm)],[c_1992]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2095,plain,
% 1.96/0.99      ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4))
% 1.96/0.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_2031]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2297,plain,
% 1.96/0.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4) != k9_tmap_1(sK3,sK4)
% 1.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK4)
% 1.96/0.99      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 1.96/0.99      | m1_subset_1(sK2(sK4,k8_tmap_1(sK3,sK4),k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK4)),u1_struct_0(sK4)) = iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1792,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_1544]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1793,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.96/0.99      | v2_struct_0(sK4)
% 1.96/0.99      | ~ l1_pre_topc(sK4)
% 1.96/0.99      | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1792]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1797,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.96/0.99      | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1793,c_38,c_37,c_1531]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2097,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.96/0.99      | k7_tmap_1(sK4,X0_57) = k6_partfun1(u1_struct_0(sK4)) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1797]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2295,plain,
% 1.96/0.99      ( k7_tmap_1(sK4,X0_57) = k6_partfun1(u1_struct_0(sK4))
% 1.96/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1774,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.99      | v2_struct_0(X1)
% 1.96/0.99      | ~ l1_pre_topc(X1)
% 1.96/0.99      | k8_tmap_1(sK3,sK4) != X1
% 1.96/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_1457]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1775,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
% 1.96/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 1.96/0.99      | k7_tmap_1(k8_tmap_1(sK3,sK4),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1774]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1779,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
% 1.96/0.99      | k7_tmap_1(k8_tmap_1(sK3,sK4),X0) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1775,c_40,c_39,c_38,c_1422,c_1466]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2098,plain,
% 1.96/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4))))
% 1.96/0.99      | k7_tmap_1(k8_tmap_1(sK3,sK4),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1779]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2294,plain,
% 1.96/0.99      ( k7_tmap_1(k8_tmap_1(sK3,sK4),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 1.96/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK3,sK4)))) != iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2098]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1608,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 1.96/0.99      | v2_struct_0(X0)
% 1.96/0.99      | ~ l1_pre_topc(X0)
% 1.96/0.99      | ~ v2_pre_topc(X0)
% 1.96/0.99      | sK3 != X0
% 1.96/0.99      | sK4 != X1 ),
% 1.96/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1609,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 1.96/0.99      | v2_struct_0(sK3)
% 1.96/0.99      | ~ l1_pre_topc(sK3)
% 1.96/0.99      | ~ v2_pre_topc(sK3) ),
% 1.96/0.99      inference(unflattening,[status(thm)],[c_1608]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_1611,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 1.96/0.99      inference(global_propositional_subsumption,
% 1.96/0.99                [status(thm)],
% 1.96/0.99                [c_1609,c_40,c_39,c_38]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2101,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_1611]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2292,plain,
% 1.96/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2101]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2105,negated_conjecture,
% 1.96/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.96/0.99      inference(subtyping,[status(esa)],[c_35]) ).
% 1.96/0.99  
% 1.96/0.99  cnf(c_2289,plain,
% 1.96/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 1.96/0.99  
% 1.96/0.99  
% 1.96/0.99  % SZS output end Saturation for theBenchmark.p
% 1.96/0.99  
% 1.96/0.99  ------                               Statistics
% 1.96/0.99  
% 1.96/0.99  ------ General
% 1.96/0.99  
% 1.96/0.99  abstr_ref_over_cycles:                  0
% 1.96/0.99  abstr_ref_under_cycles:                 0
% 1.96/0.99  gc_basic_clause_elim:                   0
% 1.96/0.99  forced_gc_time:                         0
% 1.96/0.99  parsing_time:                           0.014
% 1.96/0.99  unif_index_cands_time:                  0.
% 1.96/0.99  unif_index_add_time:                    0.
% 1.96/0.99  orderings_time:                         0.
% 1.96/0.99  out_proof_time:                         0.
% 1.96/0.99  total_time:                             0.149
% 1.96/0.99  num_of_symbols:                         65
% 1.96/0.99  num_of_terms:                           2771
% 1.96/0.99  
% 1.96/0.99  ------ Preprocessing
% 1.96/0.99  
% 1.96/0.99  num_of_splits:                          0
% 1.96/0.99  num_of_split_atoms:                     0
% 1.96/0.99  num_of_reused_defs:                     0
% 1.96/0.99  num_eq_ax_congr_red:                    14
% 1.96/0.99  num_of_sem_filtered_clauses:            1
% 1.96/0.99  num_of_subtypes:                        2
% 1.96/0.99  monotx_restored_types:                  0
% 1.96/0.99  sat_num_of_epr_types:                   0
% 1.96/0.99  sat_num_of_non_cyclic_types:            0
% 1.96/0.99  sat_guarded_non_collapsed_types:        0
% 1.96/0.99  num_pure_diseq_elim:                    0
% 1.96/0.99  simp_replaced_by:                       0
% 1.96/0.99  res_preprocessed:                       105
% 1.96/0.99  prep_upred:                             0
% 1.96/0.99  prep_unflattend:                        85
% 1.96/0.99  smt_new_axioms:                         0
% 1.96/0.99  pred_elim_cands:                        1
% 1.96/0.99  pred_elim:                              13
% 1.96/0.99  pred_elim_cl:                           28
% 1.96/0.99  pred_elim_cycles:                       20
% 1.96/0.99  merged_defs:                            0
% 1.96/0.99  merged_defs_ncl:                        0
% 1.96/0.99  bin_hyper_res:                          0
% 1.96/0.99  prep_cycles:                            4
% 1.96/0.99  pred_elim_time:                         0.051
% 1.96/0.99  splitting_time:                         0.
% 1.96/0.99  sem_filter_time:                        0.
% 1.96/0.99  monotx_time:                            0.
% 1.96/0.99  subtype_inf_time:                       0.
% 1.96/0.99  
% 1.96/0.99  ------ Problem properties
% 1.96/0.99  
% 1.96/0.99  clauses:                                11
% 1.96/0.99  conjectures:                            1
% 1.96/0.99  epr:                                    0
% 1.96/0.99  horn:                                   11
% 1.96/0.99  ground:                                 8
% 1.96/0.99  unary:                                  6
% 1.96/0.99  binary:                                 3
% 1.96/0.99  lits:                                   21
% 1.96/0.99  lits_eq:                                11
% 1.96/0.99  fd_pure:                                0
% 1.96/0.99  fd_pseudo:                              0
% 1.96/0.99  fd_cond:                                0
% 1.96/0.99  fd_pseudo_cond:                         0
% 1.96/0.99  ac_symbols:                             0
% 1.96/0.99  
% 1.96/0.99  ------ Propositional Solver
% 1.96/0.99  
% 1.96/0.99  prop_solver_calls:                      25
% 1.96/0.99  prop_fast_solver_calls:                 1246
% 1.96/0.99  smt_solver_calls:                       0
% 1.96/0.99  smt_fast_solver_calls:                  0
% 1.96/0.99  prop_num_of_clauses:                    639
% 1.96/0.99  prop_preprocess_simplified:             2743
% 1.96/0.99  prop_fo_subsumed:                       84
% 1.96/0.99  prop_solver_time:                       0.
% 1.96/0.99  smt_solver_time:                        0.
% 1.96/0.99  smt_fast_solver_time:                   0.
% 1.96/0.99  prop_fast_solver_time:                  0.
% 1.96/0.99  prop_unsat_core_time:                   0.
% 1.96/0.99  
% 1.96/0.99  ------ QBF
% 1.96/0.99  
% 1.96/0.99  qbf_q_res:                              0
% 1.96/0.99  qbf_num_tautologies:                    0
% 1.96/0.99  qbf_prep_cycles:                        0
% 1.96/0.99  
% 1.96/0.99  ------ BMC1
% 1.96/0.99  
% 1.96/0.99  bmc1_current_bound:                     -1
% 1.96/0.99  bmc1_last_solved_bound:                 -1
% 1.96/0.99  bmc1_unsat_core_size:                   -1
% 1.96/0.99  bmc1_unsat_core_parents_size:           -1
% 1.96/0.99  bmc1_merge_next_fun:                    0
% 1.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.96/0.99  
% 1.96/0.99  ------ Instantiation
% 1.96/0.99  
% 1.96/0.99  inst_num_of_clauses:                    111
% 1.96/0.99  inst_num_in_passive:                    13
% 1.96/0.99  inst_num_in_active:                     76
% 1.96/0.99  inst_num_in_unprocessed:                22
% 1.96/0.99  inst_num_of_loops:                      80
% 1.96/0.99  inst_num_of_learning_restarts:          0
% 1.96/0.99  inst_num_moves_active_passive:          2
% 1.96/0.99  inst_lit_activity:                      0
% 1.96/0.99  inst_lit_activity_moves:                0
% 1.96/0.99  inst_num_tautologies:                   0
% 1.96/0.99  inst_num_prop_implied:                  0
% 1.96/0.99  inst_num_existing_simplified:           0
% 1.96/0.99  inst_num_eq_res_simplified:             0
% 1.96/0.99  inst_num_child_elim:                    0
% 1.96/0.99  inst_num_of_dismatching_blockings:      10
% 1.96/0.99  inst_num_of_non_proper_insts:           77
% 1.96/0.99  inst_num_of_duplicates:                 0
% 1.96/0.99  inst_inst_num_from_inst_to_res:         0
% 1.96/0.99  inst_dismatching_checking_time:         0.
% 1.96/0.99  
% 1.96/0.99  ------ Resolution
% 1.96/0.99  
% 1.96/0.99  res_num_of_clauses:                     0
% 1.96/0.99  res_num_in_passive:                     0
% 1.96/0.99  res_num_in_active:                      0
% 1.96/0.99  res_num_of_loops:                       109
% 1.96/0.99  res_forward_subset_subsumed:            28
% 1.96/0.99  res_backward_subset_subsumed:           1
% 1.96/0.99  res_forward_subsumed:                   1
% 1.96/0.99  res_backward_subsumed:                  2
% 1.96/0.99  res_forward_subsumption_resolution:     14
% 1.96/0.99  res_backward_subsumption_resolution:    5
% 1.96/0.99  res_clause_to_clause_subsumption:       201
% 1.96/0.99  res_orphan_elimination:                 0
% 1.96/0.99  res_tautology_del:                      28
% 1.96/0.99  res_num_eq_res_simplified:              1
% 1.96/0.99  res_num_sel_changes:                    0
% 1.96/0.99  res_moves_from_active_to_pass:          0
% 1.96/0.99  
% 1.96/0.99  ------ Superposition
% 1.96/0.99  
% 1.96/0.99  sup_time_total:                         0.
% 1.96/0.99  sup_time_generating:                    0.
% 1.96/0.99  sup_time_sim_full:                      0.
% 1.96/0.99  sup_time_sim_immed:                     0.
% 1.96/0.99  
% 1.96/0.99  sup_num_of_clauses:                     12
% 1.96/0.99  sup_num_in_active:                      12
% 1.96/0.99  sup_num_in_passive:                     0
% 1.96/0.99  sup_num_of_loops:                       15
% 1.96/0.99  sup_fw_superposition:                   1
% 1.96/0.99  sup_bw_superposition:                   0
% 1.96/0.99  sup_immediate_simplified:               0
% 1.96/0.99  sup_given_eliminated:                   0
% 1.96/0.99  comparisons_done:                       0
% 1.96/0.99  comparisons_avoided:                    0
% 1.96/0.99  
% 1.96/0.99  ------ Simplifications
% 1.96/0.99  
% 1.96/0.99  
% 1.96/0.99  sim_fw_subset_subsumed:                 0
% 1.96/0.99  sim_bw_subset_subsumed:                 0
% 1.96/0.99  sim_fw_subsumed:                        0
% 1.96/0.99  sim_bw_subsumed:                        0
% 1.96/0.99  sim_fw_subsumption_res:                 0
% 1.96/0.99  sim_bw_subsumption_res:                 0
% 1.96/0.99  sim_tautology_del:                      0
% 1.96/0.99  sim_eq_tautology_del:                   0
% 1.96/0.99  sim_eq_res_simp:                        0
% 1.96/0.99  sim_fw_demodulated:                     0
% 1.96/0.99  sim_bw_demodulated:                     3
% 1.96/0.99  sim_light_normalised:                   3
% 1.96/0.99  sim_joinable_taut:                      0
% 1.96/0.99  sim_joinable_simp:                      0
% 1.96/0.99  sim_ac_normalised:                      0
% 1.96/0.99  sim_smt_subsumption:                    0
% 1.96/0.99  
%------------------------------------------------------------------------------
