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
% DateTime   : Thu Dec  3 12:24:07 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  229 (1706 expanded)
%              Number of clauses        :  139 ( 384 expanded)
%              Number of leaves         :   21 ( 579 expanded)
%              Depth                    :   35
%              Number of atoms          : 1150 (13277 expanded)
%              Number of equality atoms :  257 ( 660 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f61,plain,(
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

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f56,f55,f54,f53])).

fof(f91,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f67,plain,(
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

fof(f100,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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

fof(f63,plain,(
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

fof(f98,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f98])).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1186,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_1187,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1189,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_38,c_37,c_36])).

cnf(c_28,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1173,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_1174,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1176,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_36])).

cnf(c_12,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_22,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_237,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_22,c_21])).

cnf(c_940,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_34])).

cnf(c_941,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_943,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_38,c_37,c_36])).

cnf(c_944,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_943])).

cnf(c_1183,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1176,c_944])).

cnf(c_1196,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1189,c_1183])).

cnf(c_2725,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
    | k9_tmap_1(sK2,sK3) != X0
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1196])).

cnf(c_2726,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_2725])).

cnf(c_957,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_958,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_968,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_969,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_2728,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2726,c_38,c_37,c_36,c_958,c_969,c_1187])).

cnf(c_2729,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_2728])).

cnf(c_3903,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_2729])).

cnf(c_4848,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3903])).

cnf(c_8,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_247,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_28,c_20,c_19,c_18])).

cnf(c_248,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_1165,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_248,c_34])).

cnf(c_1166,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1165])).

cnf(c_1168,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_38,c_37,c_36])).

cnf(c_3940,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1168])).

cnf(c_5074,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4848,c_3940])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1175,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1174])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1781,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1782,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1781])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_38,c_36])).

cnf(c_3921,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_58)) ),
    inference(subtyping,[status(esa)],[c_1786])).

cnf(c_5254,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3921])).

cnf(c_5255,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5254])).

cnf(c_6836,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5074,c_41,c_1175,c_5255])).

cnf(c_6837,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6836])).

cnf(c_3939,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1176])).

cnf(c_4816,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3939])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1745,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1745])).

cnf(c_1750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_38,c_36])).

cnf(c_3923,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1750])).

cnf(c_4828,plain,
    ( u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3923])).

cnf(c_5839,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4816,c_4828])).

cnf(c_5841,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5839,c_3940])).

cnf(c_6840,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6837,c_5841])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3954,plain,
    ( v2_struct_0(X0_59)
    | ~ v1_xboole_0(u1_struct_0(X0_59))
    | ~ l1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4803,plain,
    ( v2_struct_0(X0_59) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_59)) != iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_5918,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5841,c_4803])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_125,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_127,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_129,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_131,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_6230,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5918,c_39,c_41,c_127,c_131])).

cnf(c_6845,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6840,c_6230])).

cnf(c_16,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1685,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_1686,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1685])).

cnf(c_1690,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1686,c_38,c_36])).

cnf(c_3926,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1690])).

cnf(c_4825,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3926])).

cnf(c_6408,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3940,c_4825])).

cnf(c_6411,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6408,c_5841])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1799])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1800,c_38,c_36])).

cnf(c_3920,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) ),
    inference(subtyping,[status(esa)],[c_1804])).

cnf(c_4831,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3920])).

cnf(c_6425,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3940,c_4831])).

cnf(c_6428,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6425,c_5841])).

cnf(c_6847,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6845,c_41,c_1175,c_6411,c_6428])).

cnf(c_14,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_443,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X2,X1) != k8_tmap_1(sK2,sK3)
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_444,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_448,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_33,c_30])).

cnf(c_449,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK4,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_1405,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK2 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_449])).

cnf(c_1406,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1405])).

cnf(c_1410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_38,c_37,c_36])).

cnf(c_1411,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1410])).

cnf(c_1552,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X2),k7_tmap_1(sK2,X2),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X2) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X1) != X2
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_1411])).

cnf(c_1553,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1)),k7_tmap_1(sK2,u1_struct_0(X1)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1552])).

cnf(c_3933,plain,
    ( ~ r1_tsep_1(X0_59,X1_59)
    | ~ m1_subset_1(u1_struct_0(X1_59),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X0_59)
    | ~ l1_struct_0(X1_59)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1_59)),k7_tmap_1(sK2,u1_struct_0(X1_59)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1_59)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_59) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1553])).

cnf(c_4822,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X0_59)),k7_tmap_1(sK2,u1_struct_0(X0_59)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X0_59)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X1_59) != u1_struct_0(sK4)
    | r1_tsep_1(X1_59,X0_59) != iProver_top
    | m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3933])).

cnf(c_6852,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k9_tmap_1(sK2,sK3),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_59) != u1_struct_0(sK4)
    | r1_tsep_1(X0_59,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6847,c_4822])).

cnf(c_6860,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_59) != u1_struct_0(sK4)
    | r1_tsep_1(X0_59,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6852,c_3940])).

cnf(c_6861,plain,
    ( u1_struct_0(X0_59) != u1_struct_0(sK4)
    | r1_tsep_1(X0_59,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6860])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1286,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_34])).

cnf(c_1287,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1286])).

cnf(c_1289,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_36])).

cnf(c_2068,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1289])).

cnf(c_2069,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2068])).

cnf(c_2070,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_7373,plain,
    ( l1_struct_0(X0_59) != iProver_top
    | u1_struct_0(X0_59) != u1_struct_0(sK4)
    | r1_tsep_1(X0_59,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6861,c_41,c_1175,c_2070])).

cnf(c_7374,plain,
    ( u1_struct_0(X0_59) != u1_struct_0(sK4)
    | r1_tsep_1(X0_59,sK3) != iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_7373])).

cnf(c_7385,plain,
    ( r1_tsep_1(sK4,sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7374])).

cnf(c_24,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3953,plain,
    ( ~ r1_tsep_1(X0_59,X1_59)
    | r1_tsep_1(X1_59,X0_59)
    | ~ l1_struct_0(X0_59)
    | ~ l1_struct_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5337,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | r1_tsep_1(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3953])).

cnf(c_5338,plain,
    ( r1_tsep_1(sK3,sK4) != iProver_top
    | r1_tsep_1(sK4,sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5337])).

cnf(c_1154,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_32])).

cnf(c_1155,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1154])).

cnf(c_1157,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_36])).

cnf(c_2054,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1157])).

cnf(c_2055,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2054])).

cnf(c_2056,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_31,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( r1_tsep_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7385,c_5338,c_2070,c_2056,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.99  
% 3.35/0.99  ------  iProver source info
% 3.35/0.99  
% 3.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.99  git: non_committed_changes: false
% 3.35/0.99  git: last_make_outside_of_git: false
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     num_symb
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       true
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  ------ Parsing...
% 3.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.99  ------ Proving...
% 3.35/0.99  ------ Problem Properties 
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  clauses                                 54
% 3.35/0.99  conjectures                             5
% 3.35/0.99  EPR                                     8
% 3.35/0.99  Horn                                    32
% 3.35/0.99  unary                                   20
% 3.35/0.99  binary                                  11
% 3.35/0.99  lits                                    148
% 3.35/0.99  lits eq                                 41
% 3.35/0.99  fd_pure                                 0
% 3.35/0.99  fd_pseudo                               0
% 3.35/0.99  fd_cond                                 6
% 3.35/0.99  fd_pseudo_cond                          0
% 3.35/0.99  AC symbols                              0
% 3.35/0.99  
% 3.35/0.99  ------ Schedule dynamic 5 is on 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ 
% 3.35/0.99  Current options:
% 3.35/0.99  ------ 
% 3.35/0.99  
% 3.35/0.99  ------ Input Options
% 3.35/0.99  
% 3.35/0.99  --out_options                           all
% 3.35/0.99  --tptp_safe_out                         true
% 3.35/0.99  --problem_path                          ""
% 3.35/0.99  --include_path                          ""
% 3.35/0.99  --clausifier                            res/vclausify_rel
% 3.35/0.99  --clausifier_options                    --mode clausify
% 3.35/0.99  --stdin                                 false
% 3.35/0.99  --stats_out                             all
% 3.35/0.99  
% 3.35/0.99  ------ General Options
% 3.35/0.99  
% 3.35/0.99  --fof                                   false
% 3.35/0.99  --time_out_real                         305.
% 3.35/0.99  --time_out_virtual                      -1.
% 3.35/0.99  --symbol_type_check                     false
% 3.35/0.99  --clausify_out                          false
% 3.35/0.99  --sig_cnt_out                           false
% 3.35/0.99  --trig_cnt_out                          false
% 3.35/0.99  --trig_cnt_out_tolerance                1.
% 3.35/0.99  --trig_cnt_out_sk_spl                   false
% 3.35/0.99  --abstr_cl_out                          false
% 3.35/0.99  
% 3.35/0.99  ------ Global Options
% 3.35/0.99  
% 3.35/0.99  --schedule                              default
% 3.35/0.99  --add_important_lit                     false
% 3.35/0.99  --prop_solver_per_cl                    1000
% 3.35/0.99  --min_unsat_core                        false
% 3.35/0.99  --soft_assumptions                      false
% 3.35/0.99  --soft_lemma_size                       3
% 3.35/0.99  --prop_impl_unit_size                   0
% 3.35/0.99  --prop_impl_unit                        []
% 3.35/0.99  --share_sel_clauses                     true
% 3.35/0.99  --reset_solvers                         false
% 3.35/0.99  --bc_imp_inh                            [conj_cone]
% 3.35/0.99  --conj_cone_tolerance                   3.
% 3.35/0.99  --extra_neg_conj                        none
% 3.35/0.99  --large_theory_mode                     true
% 3.35/0.99  --prolific_symb_bound                   200
% 3.35/0.99  --lt_threshold                          2000
% 3.35/0.99  --clause_weak_htbl                      true
% 3.35/0.99  --gc_record_bc_elim                     false
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing Options
% 3.35/0.99  
% 3.35/0.99  --preprocessing_flag                    true
% 3.35/0.99  --time_out_prep_mult                    0.1
% 3.35/0.99  --splitting_mode                        input
% 3.35/0.99  --splitting_grd                         true
% 3.35/0.99  --splitting_cvd                         false
% 3.35/0.99  --splitting_cvd_svl                     false
% 3.35/0.99  --splitting_nvd                         32
% 3.35/0.99  --sub_typing                            true
% 3.35/0.99  --prep_gs_sim                           true
% 3.35/0.99  --prep_unflatten                        true
% 3.35/0.99  --prep_res_sim                          true
% 3.35/0.99  --prep_upred                            true
% 3.35/0.99  --prep_sem_filter                       exhaustive
% 3.35/0.99  --prep_sem_filter_out                   false
% 3.35/0.99  --pred_elim                             true
% 3.35/0.99  --res_sim_input                         true
% 3.35/0.99  --eq_ax_congr_red                       true
% 3.35/0.99  --pure_diseq_elim                       true
% 3.35/0.99  --brand_transform                       false
% 3.35/0.99  --non_eq_to_eq                          false
% 3.35/0.99  --prep_def_merge                        true
% 3.35/0.99  --prep_def_merge_prop_impl              false
% 3.35/0.99  --prep_def_merge_mbd                    true
% 3.35/0.99  --prep_def_merge_tr_red                 false
% 3.35/0.99  --prep_def_merge_tr_cl                  false
% 3.35/0.99  --smt_preprocessing                     true
% 3.35/0.99  --smt_ac_axioms                         fast
% 3.35/0.99  --preprocessed_out                      false
% 3.35/0.99  --preprocessed_stats                    false
% 3.35/0.99  
% 3.35/0.99  ------ Abstraction refinement Options
% 3.35/0.99  
% 3.35/0.99  --abstr_ref                             []
% 3.35/0.99  --abstr_ref_prep                        false
% 3.35/0.99  --abstr_ref_until_sat                   false
% 3.35/0.99  --abstr_ref_sig_restrict                funpre
% 3.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.99  --abstr_ref_under                       []
% 3.35/0.99  
% 3.35/0.99  ------ SAT Options
% 3.35/0.99  
% 3.35/0.99  --sat_mode                              false
% 3.35/0.99  --sat_fm_restart_options                ""
% 3.35/0.99  --sat_gr_def                            false
% 3.35/0.99  --sat_epr_types                         true
% 3.35/0.99  --sat_non_cyclic_types                  false
% 3.35/0.99  --sat_finite_models                     false
% 3.35/0.99  --sat_fm_lemmas                         false
% 3.35/0.99  --sat_fm_prep                           false
% 3.35/0.99  --sat_fm_uc_incr                        true
% 3.35/0.99  --sat_out_model                         small
% 3.35/0.99  --sat_out_clauses                       false
% 3.35/0.99  
% 3.35/0.99  ------ QBF Options
% 3.35/0.99  
% 3.35/0.99  --qbf_mode                              false
% 3.35/0.99  --qbf_elim_univ                         false
% 3.35/0.99  --qbf_dom_inst                          none
% 3.35/0.99  --qbf_dom_pre_inst                      false
% 3.35/0.99  --qbf_sk_in                             false
% 3.35/0.99  --qbf_pred_elim                         true
% 3.35/0.99  --qbf_split                             512
% 3.35/0.99  
% 3.35/0.99  ------ BMC1 Options
% 3.35/0.99  
% 3.35/0.99  --bmc1_incremental                      false
% 3.35/0.99  --bmc1_axioms                           reachable_all
% 3.35/0.99  --bmc1_min_bound                        0
% 3.35/0.99  --bmc1_max_bound                        -1
% 3.35/0.99  --bmc1_max_bound_default                -1
% 3.35/0.99  --bmc1_symbol_reachability              true
% 3.35/0.99  --bmc1_property_lemmas                  false
% 3.35/0.99  --bmc1_k_induction                      false
% 3.35/0.99  --bmc1_non_equiv_states                 false
% 3.35/0.99  --bmc1_deadlock                         false
% 3.35/0.99  --bmc1_ucm                              false
% 3.35/0.99  --bmc1_add_unsat_core                   none
% 3.35/0.99  --bmc1_unsat_core_children              false
% 3.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.99  --bmc1_out_stat                         full
% 3.35/0.99  --bmc1_ground_init                      false
% 3.35/0.99  --bmc1_pre_inst_next_state              false
% 3.35/0.99  --bmc1_pre_inst_state                   false
% 3.35/0.99  --bmc1_pre_inst_reach_state             false
% 3.35/0.99  --bmc1_out_unsat_core                   false
% 3.35/0.99  --bmc1_aig_witness_out                  false
% 3.35/0.99  --bmc1_verbose                          false
% 3.35/0.99  --bmc1_dump_clauses_tptp                false
% 3.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.99  --bmc1_dump_file                        -
% 3.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.99  --bmc1_ucm_extend_mode                  1
% 3.35/0.99  --bmc1_ucm_init_mode                    2
% 3.35/0.99  --bmc1_ucm_cone_mode                    none
% 3.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.99  --bmc1_ucm_relax_model                  4
% 3.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.99  --bmc1_ucm_layered_model                none
% 3.35/0.99  --bmc1_ucm_max_lemma_size               10
% 3.35/0.99  
% 3.35/0.99  ------ AIG Options
% 3.35/0.99  
% 3.35/0.99  --aig_mode                              false
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation Options
% 3.35/0.99  
% 3.35/0.99  --instantiation_flag                    true
% 3.35/0.99  --inst_sos_flag                         false
% 3.35/0.99  --inst_sos_phase                        true
% 3.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.99  --inst_lit_sel_side                     none
% 3.35/0.99  --inst_solver_per_active                1400
% 3.35/0.99  --inst_solver_calls_frac                1.
% 3.35/0.99  --inst_passive_queue_type               priority_queues
% 3.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       false
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ Proving...
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS status Theorem for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  fof(f4,axiom,(
% 3.35/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f21,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.35/0.99    inference(ennf_transformation,[],[f4])).
% 3.35/0.99  
% 3.35/0.99  fof(f22,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.35/0.99    inference(flattening,[],[f21])).
% 3.35/0.99  
% 3.35/0.99  fof(f43,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.35/0.99    inference(nnf_transformation,[],[f22])).
% 3.35/0.99  
% 3.35/0.99  fof(f61,plain,(
% 3.35/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f43])).
% 3.35/0.99  
% 3.35/0.99  fof(f10,axiom,(
% 3.35/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f32,plain,(
% 3.35/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f10])).
% 3.35/0.99  
% 3.35/0.99  fof(f33,plain,(
% 3.35/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f79,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f15,conjecture,(
% 3.35/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f16,negated_conjecture,(
% 3.35/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 3.35/0.99    inference(negated_conjecture,[],[f15])).
% 3.35/0.99  
% 3.35/0.99  fof(f41,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f16])).
% 3.35/0.99  
% 3.35/0.99  fof(f42,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f41])).
% 3.35/0.99  
% 3.35/0.99  fof(f56,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f55,plain,(
% 3.35/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3) & m1_subset_1(X3,u1_struct_0(sK4))) & r1_tsep_1(X1,sK4) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f54,plain,(
% 3.35/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK3,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f53,plain,(
% 3.35/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f57,plain,(
% 3.35/0.99    (((~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) & m1_subset_1(sK5,u1_struct_0(sK4))) & r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f56,f55,f54,f53])).
% 3.35/0.99  
% 3.35/0.99  fof(f91,plain,(
% 3.35/0.99    m1_pre_topc(sK3,sK2)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f87,plain,(
% 3.35/0.99    ~v2_struct_0(sK2)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f88,plain,(
% 3.35/0.99    v2_pre_topc(sK2)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f89,plain,(
% 3.35/0.99    l1_pre_topc(sK2)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f14,axiom,(
% 3.35/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f40,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f14])).
% 3.35/0.99  
% 3.35/0.99  fof(f86,plain,(
% 3.35/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f40])).
% 3.35/0.99  
% 3.35/0.99  fof(f6,axiom,(
% 3.35/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f25,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f6])).
% 3.35/0.99  
% 3.35/0.99  fof(f26,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f25])).
% 3.35/0.99  
% 3.35/0.99  fof(f48,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f26])).
% 3.35/0.99  
% 3.35/0.99  fof(f49,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(rectify,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f50,plain,(
% 3.35/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f51,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 3.35/0.99  
% 3.35/0.99  fof(f67,plain,(
% 3.35/0.99    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f100,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f67])).
% 3.35/0.99  
% 3.35/0.99  fof(f101,plain,(
% 3.35/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f100])).
% 3.35/0.99  
% 3.35/0.99  fof(f80,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f81,plain,(
% 3.35/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f5,axiom,(
% 3.35/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f23,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f5])).
% 3.35/0.99  
% 3.35/0.99  fof(f24,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f23])).
% 3.35/0.99  
% 3.35/0.99  fof(f44,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f45,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(rectify,[],[f44])).
% 3.35/0.99  
% 3.35/0.99  fof(f46,plain,(
% 3.35/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f47,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.35/0.99  
% 3.35/0.99  fof(f63,plain,(
% 3.35/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f47])).
% 3.35/0.99  
% 3.35/0.99  fof(f98,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f63])).
% 3.35/0.99  
% 3.35/0.99  fof(f99,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f98])).
% 3.35/0.99  
% 3.35/0.99  fof(f9,axiom,(
% 3.35/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f30,plain,(
% 3.35/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f9])).
% 3.35/0.99  
% 3.35/0.99  fof(f31,plain,(
% 3.35/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f76,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f31])).
% 3.35/0.99  
% 3.35/0.99  fof(f77,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f31])).
% 3.35/0.99  
% 3.35/0.99  fof(f78,plain,(
% 3.35/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f31])).
% 3.35/0.99  
% 3.35/0.99  fof(f8,axiom,(
% 3.35/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f28,plain,(
% 3.35/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f8])).
% 3.35/0.99  
% 3.35/0.99  fof(f29,plain,(
% 3.35/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f28])).
% 3.35/0.99  
% 3.35/0.99  fof(f73,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f12,axiom,(
% 3.35/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f36,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f12])).
% 3.35/0.99  
% 3.35/0.99  fof(f37,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f36])).
% 3.35/0.99  
% 3.35/0.99  fof(f83,plain,(
% 3.35/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f37])).
% 3.35/0.99  
% 3.35/0.99  fof(f3,axiom,(
% 3.35/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f19,plain,(
% 3.35/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f3])).
% 3.35/0.99  
% 3.35/0.99  fof(f20,plain,(
% 3.35/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f19])).
% 3.35/0.99  
% 3.35/0.99  fof(f60,plain,(
% 3.35/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f20])).
% 3.35/0.99  
% 3.35/0.99  fof(f1,axiom,(
% 3.35/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f17,plain,(
% 3.35/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f1])).
% 3.35/0.99  
% 3.35/0.99  fof(f58,plain,(
% 3.35/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f17])).
% 3.35/0.99  
% 3.35/0.99  fof(f74,plain,(
% 3.35/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f75,plain,(
% 3.35/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f29])).
% 3.35/0.99  
% 3.35/0.99  fof(f7,axiom,(
% 3.35/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f27,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f7])).
% 3.35/0.99  
% 3.35/0.99  fof(f52,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.35/0.99    inference(nnf_transformation,[],[f27])).
% 3.35/0.99  
% 3.35/0.99  fof(f71,plain,(
% 3.35/0.99    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f52])).
% 3.35/0.99  
% 3.35/0.99  fof(f93,plain,(
% 3.35/0.99    m1_pre_topc(sK4,sK2)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f13,axiom,(
% 3.35/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f38,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f13])).
% 3.35/0.99  
% 3.35/0.99  fof(f39,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f38])).
% 3.35/0.99  
% 3.35/0.99  fof(f85,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f39])).
% 3.35/0.99  
% 3.35/0.99  fof(f96,plain,(
% 3.35/0.99    ~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f92,plain,(
% 3.35/0.99    ~v2_struct_0(sK4)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f95,plain,(
% 3.35/0.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  fof(f2,axiom,(
% 3.35/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f18,plain,(
% 3.35/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f2])).
% 3.35/0.99  
% 3.35/0.99  fof(f59,plain,(
% 3.35/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f18])).
% 3.35/0.99  
% 3.35/0.99  fof(f11,axiom,(
% 3.35/0.99    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f34,plain,(
% 3.35/0.99    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.35/0.99    inference(ennf_transformation,[],[f11])).
% 3.35/0.99  
% 3.35/0.99  fof(f35,plain,(
% 3.35/0.99    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.35/0.99    inference(flattening,[],[f34])).
% 3.35/0.99  
% 3.35/0.99  fof(f82,plain,(
% 3.35/0.99    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f35])).
% 3.35/0.99  
% 3.35/0.99  fof(f94,plain,(
% 3.35/0.99    r1_tsep_1(sK3,sK4)),
% 3.35/0.99    inference(cnf_transformation,[],[f57])).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4,plain,
% 3.35/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.35/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.35/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.35/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.35/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.99      | ~ v1_funct_1(X5)
% 3.35/0.99      | ~ v1_funct_1(X4)
% 3.35/0.99      | v1_xboole_0(X1)
% 3.35/0.99      | v1_xboole_0(X3)
% 3.35/0.99      | X4 = X5 ),
% 3.35/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_23,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_34,negated_conjecture,
% 3.35/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.35/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1186,plain,
% 3.35/0.99      ( ~ v2_pre_topc(X0)
% 3.35/0.99      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | sK3 != X1
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1187,plain,
% 3.35/0.99      ( ~ v2_pre_topc(sK2)
% 3.35/0.99      | v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1186]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_38,negated_conjecture,
% 3.35/0.99      ( ~ v2_struct_0(sK2) ),
% 3.35/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_37,negated_conjecture,
% 3.35/0.99      ( v2_pre_topc(sK2) ),
% 3.35/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_36,negated_conjecture,
% 3.35/0.99      ( l1_pre_topc(sK2) ),
% 3.35/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1189,plain,
% 3.35/0.99      ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1187,c_38,c_37,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_28,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1173,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | sK3 != X0
% 3.35/0.99      | sK2 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1174,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1173]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1176,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1174,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_12,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.35/0.99      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.35/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.35/0.99      | ~ m1_pre_topc(X1,X0)
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_22,plain,
% 3.35/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.35/0.99      | ~ m1_pre_topc(X1,X0)
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_21,plain,
% 3.35/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.35/0.99      | ~ m1_pre_topc(X1,X0)
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_237,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.35/0.99      | ~ m1_pre_topc(X1,X0)
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_12,c_22,c_21]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_940,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | sK3 != X1
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_237,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_941,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ v2_pre_topc(sK2)
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_940]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_943,plain,
% 3.35/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_941,c_38,c_37,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_944,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_943]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1183,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.35/0.99      inference(backward_subsumption_resolution,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1176,c_944]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1196,plain,
% 3.35/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 3.35/0.99      inference(backward_subsumption_resolution,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1189,c_1183]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2725,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.99      | ~ v1_funct_2(X3,X4,X5)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.35/0.99      | ~ v1_funct_1(X0)
% 3.35/0.99      | ~ v1_funct_1(X3)
% 3.35/0.99      | v1_xboole_0(X2)
% 3.35/0.99      | v1_xboole_0(X5)
% 3.35/0.99      | X3 = X0
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
% 3.35/0.99      | k9_tmap_1(sK2,sK3) != X0
% 3.35/0.99      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
% 3.35/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
% 3.35/0.99      | u1_struct_0(sK2) != X4
% 3.35/0.99      | u1_struct_0(sK2) != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_1196]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2726,plain,
% 3.35/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.35/0.99      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.35/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_2725]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_957,plain,
% 3.35/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | sK3 != X1
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_958,plain,
% 3.35/0.99      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | ~ v2_pre_topc(sK2)
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_957]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_968,plain,
% 3.35/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | sK3 != X1
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_969,plain,
% 3.35/0.99      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.35/0.99      | ~ v2_pre_topc(sK2)
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_968]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2728,plain,
% 3.35/0.99      ( ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_2726,c_38,c_37,c_36,c_958,c_969,c_1187]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2729,plain,
% 3.35/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.35/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_2728]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3903,plain,
% 3.35/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 3.35/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_2729]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4848,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3903]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_8,plain,
% 3.35/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.35/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_20,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_19,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_18,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_247,plain,
% 3.35/0.99      ( ~ l1_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_8,c_28,c_20,c_19,c_18]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_248,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_247]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1165,plain,
% 3.35/0.99      ( ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.35/0.99      | sK3 != X1
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_248,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1166,plain,
% 3.35/0.99      ( ~ v2_pre_topc(sK2)
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2)
% 3.35/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1165]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1168,plain,
% 3.35/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1166,c_38,c_37,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3940,plain,
% 3.35/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1168]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5074,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_4848,c_3940]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_41,plain,
% 3.35/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1175,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.35/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1174]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_17,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1781,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | sK2 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1782,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,X0))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1781]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1786,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,X0)) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1782,c_38,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3921,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,X0_58)) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1786]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5254,plain,
% 3.35/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_3921]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5255,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_5254]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6836,plain,
% 3.35/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.35/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_5074,c_41,c_1175,c_5255]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6837,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_6836]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3939,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1176]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4816,plain,
% 3.35/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3939]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_26,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1745,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.35/0.99      | sK2 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1746,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2)
% 3.35/0.99      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1745]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1750,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1746,c_38,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3923,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1750]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4828,plain,
% 3.35/0.99      ( u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2)
% 3.35/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3923]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5839,plain,
% 3.35/0.99      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_4816,c_4828]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5841,plain,
% 3.35/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_5839,c_3940]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6840,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_6837,c_5841]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2,plain,
% 3.35/0.99      ( v2_struct_0(X0)
% 3.35/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.35/0.99      | ~ l1_struct_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3954,plain,
% 3.35/0.99      ( v2_struct_0(X0_59)
% 3.35/0.99      | ~ v1_xboole_0(u1_struct_0(X0_59))
% 3.35/0.99      | ~ l1_struct_0(X0_59) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4803,plain,
% 3.35/0.99      ( v2_struct_0(X0_59) = iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(X0_59)) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3954]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5918,plain,
% 3.35/0.99      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.35/0.99      | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_5841,c_4803]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_39,plain,
% 3.35/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_125,plain,
% 3.35/0.99      ( v2_struct_0(X0) = iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.35/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_127,plain,
% 3.35/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.35/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.35/0.99      | l1_struct_0(sK2) != iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_125]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_0,plain,
% 3.35/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_129,plain,
% 3.35/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_131,plain,
% 3.35/0.99      ( l1_pre_topc(sK2) != iProver_top
% 3.35/0.99      | l1_struct_0(sK2) = iProver_top ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6230,plain,
% 3.35/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_5918,c_39,c_41,c_127,c_131]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6845,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 3.35/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.35/0.99      inference(forward_subsumption_resolution,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6840,c_6230]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_16,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.35/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.35/0.99      | ~ v2_pre_topc(X0)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1685,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.35/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X0)
% 3.35/0.99      | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1686,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1685]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1690,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1686,c_38,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3926,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58)))
% 3.35/0.99      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1690]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4825,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))) = iProver_top
% 3.35/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3926]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6408,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3940,c_4825]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6411,plain,
% 3.35/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_6408,c_5841]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_15,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1799,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | sK2 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1800,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1799]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1804,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1800,c_38,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3920,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1804]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4831,plain,
% 3.35/0.99      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3920]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6425,plain,
% 3.35/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_3940,c_4831]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6428,plain,
% 3.35/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_6425,c_5841]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6847,plain,
% 3.35/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6845,c_41,c_1175,c_6411,c_6428]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_14,plain,
% 3.35/0.99      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.35/0.99      | ~ r1_tsep_1(X0,X1)
% 3.35/0.99      | ~ l1_struct_0(X0)
% 3.35/0.99      | ~ l1_struct_0(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_32,negated_conjecture,
% 3.35/0.99      ( m1_pre_topc(sK4,sK2) ),
% 3.35/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_27,plain,
% 3.35/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 3.35/0.99      | ~ r1_xboole_0(u1_struct_0(X0),X2)
% 3.35/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_pre_topc(X0,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | ~ l1_pre_topc(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_29,negated_conjecture,
% 3.35/0.99      ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
% 3.35/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_443,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(X0),X1)
% 3.35/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.35/0.99      | ~ m1_pre_topc(X0,X2)
% 3.35/0.99      | ~ v2_pre_topc(X2)
% 3.35/0.99      | v2_struct_0(X0)
% 3.35/0.99      | v2_struct_0(X2)
% 3.35/0.99      | ~ l1_pre_topc(X2)
% 3.35/0.99      | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(X2,X1) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | sK5 != X3
% 3.35/0.99      | sK4 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_444,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.35/0.99      | ~ m1_pre_topc(sK4,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | v2_struct_0(sK4)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_33,negated_conjecture,
% 3.35/0.99      ( ~ v2_struct_0(sK4) ),
% 3.35/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_30,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_448,plain,
% 3.35/0.99      ( v2_struct_0(X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | ~ m1_pre_topc(sK4,X1)
% 3.35/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_444,c_33,c_30]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_449,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ m1_pre_topc(sK4,X1)
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_448]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1405,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.35/0.99      | ~ v2_pre_topc(X1)
% 3.35/0.99      | v2_struct_0(X1)
% 3.35/0.99      | ~ l1_pre_topc(X1)
% 3.35/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | sK2 != X1
% 3.35/0.99      | sK4 != sK4 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_449]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1406,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ v2_pre_topc(sK2)
% 3.35/0.99      | v2_struct_0(sK2)
% 3.35/0.99      | ~ l1_pre_topc(sK2)
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1405]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1410,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1406,c_38,c_37,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1411,plain,
% 3.35/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_1410]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1552,plain,
% 3.35/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.35/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ l1_struct_0(X0)
% 3.35/0.99      | ~ l1_struct_0(X1)
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X2),k7_tmap_1(sK2,X2),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,X2) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X1) != X2
% 3.35/0.99      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_1411]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1553,plain,
% 3.35/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ l1_struct_0(X0)
% 3.35/0.99      | ~ l1_struct_0(X1)
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1)),k7_tmap_1(sK2,u1_struct_0(X1)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1552]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3933,plain,
% 3.35/0.99      ( ~ r1_tsep_1(X0_59,X1_59)
% 3.35/0.99      | ~ m1_subset_1(u1_struct_0(X1_59),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.35/0.99      | ~ l1_struct_0(X0_59)
% 3.35/0.99      | ~ l1_struct_0(X1_59)
% 3.35/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1_59)),k7_tmap_1(sK2,u1_struct_0(X1_59)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,u1_struct_0(X1_59)) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X0_59) != u1_struct_0(sK4) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_1553]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4822,plain,
% 3.35/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X0_59)),k7_tmap_1(sK2,u1_struct_0(X0_59)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,u1_struct_0(X0_59)) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X1_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X1_59,X0_59) != iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(X0_59),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | l1_struct_0(X1_59) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3933]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6852,plain,
% 3.35/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k9_tmap_1(sK2,sK3),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X0_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X0_59,sK3) != iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top
% 3.35/0.99      | l1_struct_0(sK3) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_6847,c_4822]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6860,plain,
% 3.35/0.99      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 3.35/0.99      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 3.35/0.99      | u1_struct_0(X0_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X0_59,sK3) != iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top
% 3.35/0.99      | l1_struct_0(sK3) != iProver_top ),
% 3.35/0.99      inference(light_normalisation,[status(thm)],[c_6852,c_3940]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6861,plain,
% 3.35/0.99      ( u1_struct_0(X0_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X0_59,sK3) != iProver_top
% 3.35/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top
% 3.35/0.99      | l1_struct_0(sK3) != iProver_top ),
% 3.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_6860]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1,plain,
% 3.35/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1286,plain,
% 3.35/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X1 | sK2 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1287,plain,
% 3.35/0.99      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK2) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1286]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1289,plain,
% 3.35/0.99      ( l1_pre_topc(sK3) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1287,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2068,plain,
% 3.35/0.99      ( l1_struct_0(X0) | sK3 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1289]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2069,plain,
% 3.35/0.99      ( l1_struct_0(sK3) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_2068]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2070,plain,
% 3.35/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2069]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7373,plain,
% 3.35/0.99      ( l1_struct_0(X0_59) != iProver_top
% 3.35/0.99      | u1_struct_0(X0_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X0_59,sK3) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6861,c_41,c_1175,c_2070]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7374,plain,
% 3.35/0.99      ( u1_struct_0(X0_59) != u1_struct_0(sK4)
% 3.35/0.99      | r1_tsep_1(X0_59,sK3) != iProver_top
% 3.35/0.99      | l1_struct_0(X0_59) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_7373]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_7385,plain,
% 3.35/0.99      ( r1_tsep_1(sK4,sK3) != iProver_top
% 3.35/0.99      | l1_struct_0(sK4) != iProver_top ),
% 3.35/0.99      inference(equality_resolution,[status(thm)],[c_7374]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_24,plain,
% 3.35/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.35/0.99      | r1_tsep_1(X1,X0)
% 3.35/0.99      | ~ l1_struct_0(X0)
% 3.35/0.99      | ~ l1_struct_0(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3953,plain,
% 3.35/0.99      ( ~ r1_tsep_1(X0_59,X1_59)
% 3.35/0.99      | r1_tsep_1(X1_59,X0_59)
% 3.35/0.99      | ~ l1_struct_0(X0_59)
% 3.35/0.99      | ~ l1_struct_0(X1_59) ),
% 3.35/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5337,plain,
% 3.35/0.99      ( ~ r1_tsep_1(sK3,sK4)
% 3.35/0.99      | r1_tsep_1(sK4,sK3)
% 3.35/0.99      | ~ l1_struct_0(sK3)
% 3.35/0.99      | ~ l1_struct_0(sK4) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_3953]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5338,plain,
% 3.35/0.99      ( r1_tsep_1(sK3,sK4) != iProver_top
% 3.35/0.99      | r1_tsep_1(sK4,sK3) = iProver_top
% 3.35/0.99      | l1_struct_0(sK3) != iProver_top
% 3.35/0.99      | l1_struct_0(sK4) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_5337]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1154,plain,
% 3.35/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_32]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1155,plain,
% 3.35/0.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1154]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1157,plain,
% 3.35/0.99      ( l1_pre_topc(sK4) ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1155,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2054,plain,
% 3.35/0.99      ( l1_struct_0(X0) | sK4 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1157]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2055,plain,
% 3.35/0.99      ( l1_struct_0(sK4) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_2054]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2056,plain,
% 3.35/0.99      ( l1_struct_0(sK4) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_31,negated_conjecture,
% 3.35/0.99      ( r1_tsep_1(sK3,sK4) ),
% 3.35/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_46,plain,
% 3.35/0.99      ( r1_tsep_1(sK3,sK4) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(contradiction,plain,
% 3.35/0.99      ( $false ),
% 3.35/0.99      inference(minisat,[status(thm)],[c_7385,c_5338,c_2070,c_2056,c_46]) ).
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  ------                               Statistics
% 3.35/0.99  
% 3.35/0.99  ------ General
% 3.35/0.99  
% 3.35/0.99  abstr_ref_over_cycles:                  0
% 3.35/0.99  abstr_ref_under_cycles:                 0
% 3.35/0.99  gc_basic_clause_elim:                   0
% 3.35/0.99  forced_gc_time:                         0
% 3.35/0.99  parsing_time:                           0.016
% 3.35/0.99  unif_index_cands_time:                  0.
% 3.35/0.99  unif_index_add_time:                    0.
% 3.35/0.99  orderings_time:                         0.
% 3.35/0.99  out_proof_time:                         0.018
% 3.35/0.99  total_time:                             0.302
% 3.35/0.99  num_of_symbols:                         68
% 3.35/0.99  num_of_terms:                           6382
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing
% 3.35/0.99  
% 3.35/0.99  num_of_splits:                          0
% 3.35/0.99  num_of_split_atoms:                     0
% 3.35/0.99  num_of_reused_defs:                     0
% 3.35/0.99  num_eq_ax_congr_red:                    12
% 3.35/0.99  num_of_sem_filtered_clauses:            8
% 3.35/0.99  num_of_subtypes:                        4
% 3.35/0.99  monotx_restored_types:                  0
% 3.35/0.99  sat_num_of_epr_types:                   0
% 3.35/0.99  sat_num_of_non_cyclic_types:            0
% 3.35/0.99  sat_guarded_non_collapsed_types:        1
% 3.35/0.99  num_pure_diseq_elim:                    0
% 3.35/0.99  simp_replaced_by:                       0
% 3.35/0.99  res_preprocessed:                       195
% 3.35/0.99  prep_upred:                             0
% 3.35/0.99  prep_unflattend:                        188
% 3.35/0.99  smt_new_axioms:                         0
% 3.35/0.99  pred_elim_cands:                        14
% 3.35/0.99  pred_elim:                              7
% 3.35/0.99  pred_elim_cl:                           -15
% 3.35/0.99  pred_elim_cycles:                       12
% 3.35/0.99  merged_defs:                            0
% 3.35/0.99  merged_defs_ncl:                        0
% 3.35/0.99  bin_hyper_res:                          0
% 3.35/0.99  prep_cycles:                            3
% 3.35/0.99  pred_elim_time:                         0.114
% 3.35/0.99  splitting_time:                         0.
% 3.35/0.99  sem_filter_time:                        0.
% 3.35/0.99  monotx_time:                            0.
% 3.35/0.99  subtype_inf_time:                       0.001
% 3.35/0.99  
% 3.35/0.99  ------ Problem properties
% 3.35/0.99  
% 3.35/0.99  clauses:                                54
% 3.35/0.99  conjectures:                            5
% 3.35/0.99  epr:                                    8
% 3.35/0.99  horn:                                   32
% 3.35/0.99  ground:                                 30
% 3.35/0.99  unary:                                  20
% 3.35/0.99  binary:                                 11
% 3.35/0.99  lits:                                   148
% 3.35/0.99  lits_eq:                                41
% 3.35/0.99  fd_pure:                                0
% 3.35/0.99  fd_pseudo:                              0
% 3.35/0.99  fd_cond:                                6
% 3.35/0.99  fd_pseudo_cond:                         0
% 3.35/0.99  ac_symbols:                             0
% 3.35/0.99  
% 3.35/0.99  ------ Propositional Solver
% 3.35/0.99  
% 3.35/0.99  prop_solver_calls:                      22
% 3.35/0.99  prop_fast_solver_calls:                 2447
% 3.35/0.99  smt_solver_calls:                       0
% 3.35/0.99  smt_fast_solver_calls:                  0
% 3.35/0.99  prop_num_of_clauses:                    1888
% 3.35/0.99  prop_preprocess_simplified:             6516
% 3.35/0.99  prop_fo_subsumed:                       174
% 3.35/0.99  prop_solver_time:                       0.
% 3.35/0.99  smt_solver_time:                        0.
% 3.35/0.99  smt_fast_solver_time:                   0.
% 3.35/0.99  prop_fast_solver_time:                  0.
% 3.35/0.99  prop_unsat_core_time:                   0.
% 3.35/0.99  
% 3.35/0.99  ------ QBF
% 3.35/0.99  
% 3.35/0.99  qbf_q_res:                              0
% 3.35/0.99  qbf_num_tautologies:                    0
% 3.35/0.99  qbf_prep_cycles:                        0
% 3.35/0.99  
% 3.35/0.99  ------ BMC1
% 3.35/0.99  
% 3.35/0.99  bmc1_current_bound:                     -1
% 3.35/0.99  bmc1_last_solved_bound:                 -1
% 3.35/0.99  bmc1_unsat_core_size:                   -1
% 3.35/0.99  bmc1_unsat_core_parents_size:           -1
% 3.35/0.99  bmc1_merge_next_fun:                    0
% 3.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation
% 3.35/0.99  
% 3.35/0.99  inst_num_of_clauses:                    421
% 3.35/0.99  inst_num_in_passive:                    48
% 3.35/0.99  inst_num_in_active:                     263
% 3.35/0.99  inst_num_in_unprocessed:                110
% 3.35/0.99  inst_num_of_loops:                      290
% 3.35/0.99  inst_num_of_learning_restarts:          0
% 3.35/0.99  inst_num_moves_active_passive:          25
% 3.35/0.99  inst_lit_activity:                      0
% 3.35/0.99  inst_lit_activity_moves:                0
% 3.35/0.99  inst_num_tautologies:                   0
% 3.35/0.99  inst_num_prop_implied:                  0
% 3.35/0.99  inst_num_existing_simplified:           0
% 3.35/0.99  inst_num_eq_res_simplified:             0
% 3.35/0.99  inst_num_child_elim:                    0
% 3.35/0.99  inst_num_of_dismatching_blockings:      49
% 3.35/0.99  inst_num_of_non_proper_insts:           333
% 3.35/0.99  inst_num_of_duplicates:                 0
% 3.35/0.99  inst_inst_num_from_inst_to_res:         0
% 3.35/0.99  inst_dismatching_checking_time:         0.
% 3.35/0.99  
% 3.35/0.99  ------ Resolution
% 3.35/0.99  
% 3.35/0.99  res_num_of_clauses:                     0
% 3.35/0.99  res_num_in_passive:                     0
% 3.35/0.99  res_num_in_active:                      0
% 3.35/0.99  res_num_of_loops:                       198
% 3.35/0.99  res_forward_subset_subsumed:            58
% 3.35/0.99  res_backward_subset_subsumed:           0
% 3.35/0.99  res_forward_subsumed:                   1
% 3.35/0.99  res_backward_subsumed:                  0
% 3.35/0.99  res_forward_subsumption_resolution:     12
% 3.35/0.99  res_backward_subsumption_resolution:    4
% 3.35/0.99  res_clause_to_clause_subsumption:       488
% 3.35/0.99  res_orphan_elimination:                 0
% 3.35/0.99  res_tautology_del:                      74
% 3.35/0.99  res_num_eq_res_simplified:              0
% 3.35/0.99  res_num_sel_changes:                    0
% 3.35/0.99  res_moves_from_active_to_pass:          0
% 3.35/0.99  
% 3.35/0.99  ------ Superposition
% 3.35/0.99  
% 3.35/0.99  sup_time_total:                         0.
% 3.35/0.99  sup_time_generating:                    0.
% 3.35/0.99  sup_time_sim_full:                      0.
% 3.35/0.99  sup_time_sim_immed:                     0.
% 3.35/0.99  
% 3.35/0.99  sup_num_of_clauses:                     81
% 3.35/0.99  sup_num_in_active:                      51
% 3.35/0.99  sup_num_in_passive:                     30
% 3.35/0.99  sup_num_of_loops:                       57
% 3.35/0.99  sup_fw_superposition:                   20
% 3.35/0.99  sup_bw_superposition:                   30
% 3.35/0.99  sup_immediate_simplified:               29
% 3.35/0.99  sup_given_eliminated:                   0
% 3.35/0.99  comparisons_done:                       0
% 3.35/0.99  comparisons_avoided:                    5
% 3.35/0.99  
% 3.35/0.99  ------ Simplifications
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  sim_fw_subset_subsumed:                 8
% 3.35/0.99  sim_bw_subset_subsumed:                 0
% 3.35/0.99  sim_fw_subsumed:                        0
% 3.35/0.99  sim_bw_subsumed:                        0
% 3.35/0.99  sim_fw_subsumption_res:                 4
% 3.35/0.99  sim_bw_subsumption_res:                 0
% 3.35/0.99  sim_tautology_del:                      2
% 3.35/0.99  sim_eq_tautology_del:                   5
% 3.35/0.99  sim_eq_res_simp:                        4
% 3.35/0.99  sim_fw_demodulated:                     0
% 3.35/0.99  sim_bw_demodulated:                     7
% 3.35/0.99  sim_light_normalised:                   41
% 3.35/0.99  sim_joinable_taut:                      0
% 3.35/0.99  sim_joinable_simp:                      0
% 3.35/0.99  sim_ac_normalised:                      0
% 3.35/0.99  sim_smt_subsumption:                    0
% 3.35/0.99  
%------------------------------------------------------------------------------
