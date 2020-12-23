%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:18 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  119 (2265 expanded)
%              Number of clauses        :   69 ( 223 expanded)
%              Number of leaves         :   12 ( 784 expanded)
%              Depth                    :   20
%              Number of atoms          :  881 (29536 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( v5_pre_topc(X2,X1,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK8)
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(X1,X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            | ~ v5_pre_topc(X2,X1,X0) )
          & ( ! [X4] :
                ( r1_tmap_1(X1,X0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | v5_pre_topc(X2,X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tmap_1(X1,X0,sK7,X3)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ v5_pre_topc(sK7,X1,X0) )
        & ( ! [X4] :
              ( r1_tmap_1(X1,X0,sK7,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | v5_pre_topc(sK7,X1,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK7,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(sK6,X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK6)) )
              | ~ v5_pre_topc(X2,sK6,X0) )
            & ( ! [X4] :
                  ( r1_tmap_1(sK6,X0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
              | v5_pre_topc(X2,sK6,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | v5_pre_topc(X2,X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,sK5,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,sK5) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,sK5,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,sK5) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( ~ r1_tmap_1(sK6,sK5,sK7,sK8)
        & m1_subset_1(sK8,u1_struct_0(sK6)) )
      | ~ v5_pre_topc(sK7,sK6,sK5) )
    & ( ! [X4] :
          ( r1_tmap_1(sK6,sK5,sK7,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
      | v5_pre_topc(sK7,sK6,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f28,f27,f26,f25])).

fof(f48,plain,(
    ! [X4] :
      ( r1_tmap_1(sK6,sK5,sK7,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK6))
      | v5_pre_topc(sK7,sK6,sK5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
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
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ? [X8] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
                              & m1_connsp_2(X8,X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X7,X6,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
          & m1_connsp_2(X8,X0,X6) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7)
        & m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                  | ~ m1_connsp_2(X5,X0,X3) )
              & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ! [X5] :
                ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2)) )
            & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ! [X5] :
                        ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2))
                        | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2)) )
                    & m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)))
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7)
                            & m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
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
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & m1_connsp_2(X7,X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f11])).

fof(f14,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & m1_connsp_2(X7,X0,X3) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
        & m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
                            | ~ m1_connsp_2(X5,X0,X3) )
                        & m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
                            & m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f30,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3)
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ v5_pre_topc(sK7,sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6)
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
      | ~ m1_connsp_2(X5,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,sK8)
    | ~ v5_pre_topc(sK7,sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7)
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X5,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2))
      | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,sK7,X0)
    | v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_492,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | m1_subset_1(sK2(sK6,sK5,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_6,c_13])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_494,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | m1_subset_1(sK2(sK6,sK5,sK7),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_1256,plain,
    ( r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
    | v5_pre_topc(sK7,sK6,sK5) ),
    inference(resolution,[status(thm)],[c_11,c_494])).

cnf(c_3,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | m1_connsp_2(sK1(X0,X1,X2,X3,X4),X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_357,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | m1_connsp_2(sK1(sK6,sK5,sK7,X0,X1),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_361,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | m1_connsp_2(sK1(sK6,sK5,sK7,X0,X1),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_1239,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
    | v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0),sK6,sK2(sK6,sK5,sK7)) ),
    inference(resolution,[status(thm)],[c_361,c_494])).

cnf(c_1264,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0),sK6,sK2(sK6,sK5,sK7)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1256,c_1239])).

cnf(c_1633,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0_54,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0_54),sK6,sK2(sK6,sK5,sK7)) ),
    inference(subtyping,[status(esa)],[c_1264])).

cnf(c_1668,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
    | ~ m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_10,negated_conjecture,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_connsp_2(X3,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X4))
    | m1_connsp_2(sK4(X1,X2,X0,X4,X3),X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_446,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
    | m1_connsp_2(sK4(sK6,sK5,sK7,X1,X0),sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_450,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
    | m1_connsp_2(sK4(sK6,sK5,sK7,X1,X0),sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_1179,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
    | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,X0),sK6,sK8) ),
    inference(resolution,[status(thm)],[c_10,c_450])).

cnf(c_1634,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0_54,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
    | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,X0_54),sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_1179])).

cnf(c_1665,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
    | ~ m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_0,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X4,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),sK0(X0,X1,X2,X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_423,plain,
    ( r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_427,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0))
    | r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_428,plain,
    ( r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0)) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_1132,plain,
    ( r1_tmap_1(sK6,sK5,sK7,sK8)
    | ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK8)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tmap_1(sK6,sK5,sK7,sK8)
    | ~ v5_pre_topc(sK7,sK6,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_771,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_9,c_428])).

cnf(c_775,plain,
    ( ~ m1_connsp_2(X0,sK6,sK8)
    | ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_10])).

cnf(c_776,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK8)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
    inference(renaming,[status(thm)],[c_775])).

cnf(c_1135,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK8)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_776])).

cnf(c_7,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_connsp_2(X3,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK4(X1,X2,X0,X4,X3)),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_469,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_7,c_13])).

cnf(c_473,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0)
    | ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_474,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1165,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,sK8,X0)),X0) ),
    inference(resolution,[status(thm)],[c_10,c_474])).

cnf(c_1315,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
    | ~ m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_1135,c_1165])).

cnf(c_1,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_403,plain,
    ( r1_tmap_1(sK6,sK5,sK7,X0)
    | m1_connsp_2(sK0(sK6,sK5,sK7,X0),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_407,plain,
    ( r1_tmap_1(sK6,sK5,sK7,X0)
    | m1_connsp_2(sK0(sK6,sK5,sK7,X0),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_791,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_9,c_407])).

cnf(c_1317,plain,
    ( ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
    | ~ v5_pre_topc(sK7,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1315,c_10,c_791])).

cnf(c_1318,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8) ),
    inference(renaming,[status(thm)],[c_1317])).

cnf(c_4,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_connsp_2(X3,X1,sK2(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),sK3(X1,X2,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_518,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_522,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7))
    | v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_523,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_2,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X4)),X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_380,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_384,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1)
    | ~ r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(c_385,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
    | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1) ),
    inference(renaming,[status(thm)],[c_384])).

cnf(c_1222,plain,
    ( ~ r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
    | v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0)),X0) ),
    inference(resolution,[status(thm)],[c_385,c_494])).

cnf(c_1263,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0)),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1256,c_1222])).

cnf(c_1302,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
    | ~ m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
    inference(resolution,[status(thm)],[c_523,c_1263])).

cnf(c_5,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | m1_connsp_2(sK3(X1,X2,X0),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_505,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK7) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_1304,plain,
    ( ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
    | v5_pre_topc(sK7,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1302,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12,c_505])).

cnf(c_1305,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_1304])).

cnf(c_793,plain,
    ( m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
    | ~ v5_pre_topc(sK7,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_791,c_10])).

cnf(c_794,plain,
    ( ~ v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
    inference(renaming,[status(thm)],[c_793])).

cnf(c_507,plain,
    ( v5_pre_topc(sK7,sK6,sK5)
    | m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1668,c_1665,c_1318,c_1305,c_794,c_507])).


%------------------------------------------------------------------------------
