%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:16 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 1.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/0.99  
% 1.18/0.99  ------  iProver source info
% 1.18/0.99  
% 1.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/0.99  git: non_committed_changes: false
% 1.18/0.99  git: last_make_outside_of_git: false
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/0.99  --sat_gr_def                            false
% 1.18/0.99  --sat_epr_types                         true
% 1.18/0.99  --sat_non_cyclic_types                  false
% 1.18/0.99  --sat_finite_models                     false
% 1.18/0.99  --sat_fm_lemmas                         false
% 1.18/0.99  --sat_fm_prep                           false
% 1.18/0.99  --sat_fm_uc_incr                        true
% 1.18/0.99  --sat_out_model                         small
% 1.18/0.99  --sat_out_clauses                       false
% 1.18/0.99  
% 1.18/0.99  ------ QBF Options
% 1.18/0.99  
% 1.18/0.99  --qbf_mode                              false
% 1.18/0.99  --qbf_elim_univ                         false
% 1.18/0.99  --qbf_dom_inst                          none
% 1.18/0.99  --qbf_dom_pre_inst                      false
% 1.18/0.99  --qbf_sk_in                             false
% 1.18/0.99  --qbf_pred_elim                         true
% 1.18/0.99  --qbf_split                             512
% 1.18/0.99  
% 1.18/0.99  ------ BMC1 Options
% 1.18/0.99  
% 1.18/0.99  --bmc1_incremental                      false
% 1.18/0.99  --bmc1_axioms                           reachable_all
% 1.18/0.99  --bmc1_min_bound                        0
% 1.18/0.99  --bmc1_max_bound                        -1
% 1.18/0.99  --bmc1_max_bound_default                -1
% 1.18/0.99  --bmc1_symbol_reachability              true
% 1.18/0.99  --bmc1_property_lemmas                  false
% 1.18/0.99  --bmc1_k_induction                      false
% 1.18/0.99  --bmc1_non_equiv_states                 false
% 1.18/0.99  --bmc1_deadlock                         false
% 1.18/0.99  --bmc1_ucm                              false
% 1.18/0.99  --bmc1_add_unsat_core                   none
% 1.18/0.99  --bmc1_unsat_core_children              false
% 1.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.99  --bmc1_out_stat                         full
% 1.18/0.99  --bmc1_ground_init                      false
% 1.18/0.99  --bmc1_pre_inst_next_state              false
% 1.18/0.99  --bmc1_pre_inst_state                   false
% 1.18/0.99  --bmc1_pre_inst_reach_state             false
% 1.18/0.99  --bmc1_out_unsat_core                   false
% 1.18/0.99  --bmc1_aig_witness_out                  false
% 1.18/0.99  --bmc1_verbose                          false
% 1.18/0.99  --bmc1_dump_clauses_tptp                false
% 1.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.99  --bmc1_dump_file                        -
% 1.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.99  --bmc1_ucm_extend_mode                  1
% 1.18/0.99  --bmc1_ucm_init_mode                    2
% 1.18/0.99  --bmc1_ucm_cone_mode                    none
% 1.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.99  --bmc1_ucm_relax_model                  4
% 1.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.99  --bmc1_ucm_layered_model                none
% 1.18/0.99  --bmc1_ucm_max_lemma_size               10
% 1.18/0.99  
% 1.18/0.99  ------ AIG Options
% 1.18/0.99  
% 1.18/0.99  --aig_mode                              false
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation Options
% 1.18/0.99  
% 1.18/0.99  --instantiation_flag                    true
% 1.18/0.99  --inst_sos_flag                         false
% 1.18/0.99  --inst_sos_phase                        true
% 1.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel_side                     num_symb
% 1.18/0.99  --inst_solver_per_active                1400
% 1.18/0.99  --inst_solver_calls_frac                1.
% 1.18/0.99  --inst_passive_queue_type               priority_queues
% 1.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.99  --inst_passive_queues_freq              [25;2]
% 1.18/0.99  --inst_dismatching                      true
% 1.18/0.99  --inst_eager_unprocessed_to_passive     true
% 1.18/0.99  --inst_prop_sim_given                   true
% 1.18/0.99  --inst_prop_sim_new                     false
% 1.18/0.99  --inst_subs_new                         false
% 1.18/0.99  --inst_eq_res_simp                      false
% 1.18/0.99  --inst_subs_given                       false
% 1.18/0.99  --inst_orphan_elimination               true
% 1.18/0.99  --inst_learning_loop_flag               true
% 1.18/0.99  --inst_learning_start                   3000
% 1.18/0.99  --inst_learning_factor                  2
% 1.18/0.99  --inst_start_prop_sim_after_learn       3
% 1.18/0.99  --inst_sel_renew                        solver
% 1.18/0.99  --inst_lit_activity_flag                true
% 1.18/0.99  --inst_restr_to_given                   false
% 1.18/0.99  --inst_activity_threshold               500
% 1.18/0.99  --inst_out_proof                        true
% 1.18/0.99  
% 1.18/0.99  ------ Resolution Options
% 1.18/0.99  
% 1.18/0.99  --resolution_flag                       true
% 1.18/0.99  --res_lit_sel                           adaptive
% 1.18/0.99  --res_lit_sel_side                      none
% 1.18/0.99  --res_ordering                          kbo
% 1.18/0.99  --res_to_prop_solver                    active
% 1.18/0.99  --res_prop_simpl_new                    false
% 1.18/0.99  --res_prop_simpl_given                  true
% 1.18/0.99  --res_passive_queue_type                priority_queues
% 1.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.99  --res_passive_queues_freq               [15;5]
% 1.18/0.99  --res_forward_subs                      full
% 1.18/0.99  --res_backward_subs                     full
% 1.18/0.99  --res_forward_subs_resolution           true
% 1.18/0.99  --res_backward_subs_resolution          true
% 1.18/0.99  --res_orphan_elimination                true
% 1.18/0.99  --res_time_limit                        2.
% 1.18/0.99  --res_out_proof                         true
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Options
% 1.18/0.99  
% 1.18/0.99  --superposition_flag                    true
% 1.18/0.99  --sup_passive_queue_type                priority_queues
% 1.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.99  --demod_completeness_check              fast
% 1.18/0.99  --demod_use_ground                      true
% 1.18/0.99  --sup_to_prop_solver                    passive
% 1.18/0.99  --sup_prop_simpl_new                    true
% 1.18/0.99  --sup_prop_simpl_given                  true
% 1.18/0.99  --sup_fun_splitting                     false
% 1.18/0.99  --sup_smt_interval                      50000
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Simplification Setup
% 1.18/0.99  
% 1.18/0.99  --sup_indices_passive                   []
% 1.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_full_bw                           [BwDemod]
% 1.18/0.99  --sup_immed_triv                        [TrivRules]
% 1.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_immed_bw_main                     []
% 1.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  
% 1.18/0.99  ------ Combination Options
% 1.18/0.99  
% 1.18/0.99  --comb_res_mult                         3
% 1.18/0.99  --comb_sup_mult                         2
% 1.18/0.99  --comb_inst_mult                        10
% 1.18/0.99  
% 1.18/0.99  ------ Debug Options
% 1.18/0.99  
% 1.18/0.99  --dbg_backtrace                         false
% 1.18/0.99  --dbg_dump_prop_clauses                 false
% 1.18/0.99  --dbg_dump_prop_clauses_file            -
% 1.18/0.99  --dbg_out_stat                          false
% 1.18/0.99  ------ Parsing...
% 1.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/0.99  ------ Proving...
% 1.18/0.99  ------ Problem Properties 
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  clauses                                 6
% 1.18/0.99  conjectures                             0
% 1.18/0.99  EPR                                     0
% 1.18/0.99  Horn                                    4
% 1.18/0.99  unary                                   0
% 1.18/0.99  binary                                  4
% 1.18/0.99  lits                                    14
% 1.18/0.99  lits eq                                 0
% 1.18/0.99  fd_pure                                 0
% 1.18/0.99  fd_pseudo                               0
% 1.18/0.99  fd_cond                                 0
% 1.18/0.99  fd_pseudo_cond                          0
% 1.18/0.99  AC symbols                              0
% 1.18/0.99  
% 1.18/0.99  ------ Schedule dynamic 5 is on 
% 1.18/0.99  
% 1.18/0.99  ------ no conjectures: strip conj schedule 
% 1.18/0.99  
% 1.18/0.99  ------ no equalities: superposition off 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  Current options:
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/0.99  --sat_gr_def                            false
% 1.18/0.99  --sat_epr_types                         true
% 1.18/0.99  --sat_non_cyclic_types                  false
% 1.18/0.99  --sat_finite_models                     false
% 1.18/0.99  --sat_fm_lemmas                         false
% 1.18/0.99  --sat_fm_prep                           false
% 1.18/0.99  --sat_fm_uc_incr                        true
% 1.18/0.99  --sat_out_model                         small
% 1.18/0.99  --sat_out_clauses                       false
% 1.18/0.99  
% 1.18/0.99  ------ QBF Options
% 1.18/0.99  
% 1.18/0.99  --qbf_mode                              false
% 1.18/0.99  --qbf_elim_univ                         false
% 1.18/0.99  --qbf_dom_inst                          none
% 1.18/0.99  --qbf_dom_pre_inst                      false
% 1.18/0.99  --qbf_sk_in                             false
% 1.18/0.99  --qbf_pred_elim                         true
% 1.18/0.99  --qbf_split                             512
% 1.18/0.99  
% 1.18/0.99  ------ BMC1 Options
% 1.18/0.99  
% 1.18/0.99  --bmc1_incremental                      false
% 1.18/0.99  --bmc1_axioms                           reachable_all
% 1.18/0.99  --bmc1_min_bound                        0
% 1.18/0.99  --bmc1_max_bound                        -1
% 1.18/0.99  --bmc1_max_bound_default                -1
% 1.18/0.99  --bmc1_symbol_reachability              true
% 1.18/0.99  --bmc1_property_lemmas                  false
% 1.18/0.99  --bmc1_k_induction                      false
% 1.18/0.99  --bmc1_non_equiv_states                 false
% 1.18/0.99  --bmc1_deadlock                         false
% 1.18/0.99  --bmc1_ucm                              false
% 1.18/0.99  --bmc1_add_unsat_core                   none
% 1.18/0.99  --bmc1_unsat_core_children              false
% 1.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.99  --bmc1_out_stat                         full
% 1.18/0.99  --bmc1_ground_init                      false
% 1.18/0.99  --bmc1_pre_inst_next_state              false
% 1.18/0.99  --bmc1_pre_inst_state                   false
% 1.18/0.99  --bmc1_pre_inst_reach_state             false
% 1.18/0.99  --bmc1_out_unsat_core                   false
% 1.18/0.99  --bmc1_aig_witness_out                  false
% 1.18/0.99  --bmc1_verbose                          false
% 1.18/0.99  --bmc1_dump_clauses_tptp                false
% 1.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.99  --bmc1_dump_file                        -
% 1.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.99  --bmc1_ucm_extend_mode                  1
% 1.18/0.99  --bmc1_ucm_init_mode                    2
% 1.18/0.99  --bmc1_ucm_cone_mode                    none
% 1.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.99  --bmc1_ucm_relax_model                  4
% 1.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.99  --bmc1_ucm_layered_model                none
% 1.18/0.99  --bmc1_ucm_max_lemma_size               10
% 1.18/0.99  
% 1.18/0.99  ------ AIG Options
% 1.18/0.99  
% 1.18/0.99  --aig_mode                              false
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation Options
% 1.18/0.99  
% 1.18/0.99  --instantiation_flag                    true
% 1.18/0.99  --inst_sos_flag                         false
% 1.18/0.99  --inst_sos_phase                        true
% 1.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel_side                     none
% 1.18/0.99  --inst_solver_per_active                1400
% 1.18/0.99  --inst_solver_calls_frac                1.
% 1.18/0.99  --inst_passive_queue_type               priority_queues
% 1.18/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.18/0.99  --inst_passive_queues_freq              [25;2]
% 1.18/0.99  --inst_dismatching                      true
% 1.18/0.99  --inst_eager_unprocessed_to_passive     true
% 1.18/0.99  --inst_prop_sim_given                   true
% 1.18/0.99  --inst_prop_sim_new                     false
% 1.18/0.99  --inst_subs_new                         false
% 1.18/0.99  --inst_eq_res_simp                      false
% 1.18/0.99  --inst_subs_given                       false
% 1.18/0.99  --inst_orphan_elimination               true
% 1.18/0.99  --inst_learning_loop_flag               true
% 1.18/0.99  --inst_learning_start                   3000
% 1.18/0.99  --inst_learning_factor                  2
% 1.18/0.99  --inst_start_prop_sim_after_learn       3
% 1.18/0.99  --inst_sel_renew                        solver
% 1.18/0.99  --inst_lit_activity_flag                true
% 1.18/0.99  --inst_restr_to_given                   false
% 1.18/0.99  --inst_activity_threshold               500
% 1.18/0.99  --inst_out_proof                        true
% 1.18/0.99  
% 1.18/0.99  ------ Resolution Options
% 1.18/0.99  
% 1.18/0.99  --resolution_flag                       false
% 1.18/0.99  --res_lit_sel                           adaptive
% 1.18/0.99  --res_lit_sel_side                      none
% 1.18/0.99  --res_ordering                          kbo
% 1.18/0.99  --res_to_prop_solver                    active
% 1.18/0.99  --res_prop_simpl_new                    false
% 1.18/0.99  --res_prop_simpl_given                  true
% 1.18/0.99  --res_passive_queue_type                priority_queues
% 1.18/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.18/0.99  --res_passive_queues_freq               [15;5]
% 1.18/0.99  --res_forward_subs                      full
% 1.18/0.99  --res_backward_subs                     full
% 1.18/0.99  --res_forward_subs_resolution           true
% 1.18/0.99  --res_backward_subs_resolution          true
% 1.18/0.99  --res_orphan_elimination                true
% 1.18/0.99  --res_time_limit                        2.
% 1.18/0.99  --res_out_proof                         true
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Options
% 1.18/0.99  
% 1.18/0.99  --superposition_flag                    false
% 1.18/0.99  --sup_passive_queue_type                priority_queues
% 1.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.99  --demod_completeness_check              fast
% 1.18/0.99  --demod_use_ground                      true
% 1.18/0.99  --sup_to_prop_solver                    passive
% 1.18/0.99  --sup_prop_simpl_new                    true
% 1.18/0.99  --sup_prop_simpl_given                  true
% 1.18/0.99  --sup_fun_splitting                     false
% 1.18/0.99  --sup_smt_interval                      50000
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Simplification Setup
% 1.18/0.99  
% 1.18/0.99  --sup_indices_passive                   []
% 1.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_full_bw                           [BwDemod]
% 1.18/0.99  --sup_immed_triv                        [TrivRules]
% 1.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_immed_bw_main                     []
% 1.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  
% 1.18/0.99  ------ Combination Options
% 1.18/0.99  
% 1.18/0.99  --comb_res_mult                         3
% 1.18/0.99  --comb_sup_mult                         2
% 1.18/0.99  --comb_inst_mult                        10
% 1.18/0.99  
% 1.18/0.99  ------ Debug Options
% 1.18/0.99  
% 1.18/0.99  --dbg_backtrace                         false
% 1.18/0.99  --dbg_dump_prop_clauses                 false
% 1.18/0.99  --dbg_dump_prop_clauses_file            -
% 1.18/0.99  --dbg_out_stat                          false
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  ------ Proving...
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  % SZS status Theorem for theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  fof(f3,conjecture,(
% 1.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f4,negated_conjecture,(
% 1.18/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 1.18/0.99    inference(negated_conjecture,[],[f3])).
% 1.18/0.99  
% 1.18/0.99  fof(f9,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : ((v5_pre_topc(X2,X1,X0) <~> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f4])).
% 1.18/0.99  
% 1.18/0.99  fof(f10,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : ((v5_pre_topc(X2,X1,X0) <~> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f9])).
% 1.18/0.99  
% 1.18/0.99  fof(f22,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.99    inference(nnf_transformation,[],[f10])).
% 1.18/0.99  
% 1.18/0.99  fof(f23,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f22])).
% 1.18/0.99  
% 1.18/0.99  fof(f24,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.18/0.99    inference(rectify,[],[f23])).
% 1.18/0.99  
% 1.18/0.99  fof(f28,plain,(
% 1.18/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK8) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f27,plain,(
% 1.18/0.99    ( ! [X0,X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ((? [X3] : (~r1_tmap_1(X1,X0,sK7,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(sK7,X1,X0)) & (! [X4] : (r1_tmap_1(X1,X0,sK7,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(sK7,X1,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK7,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f26,plain,(
% 1.18/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (~r1_tmap_1(sK6,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) | ~v5_pre_topc(X2,sK6,X0)) & (! [X4] : (r1_tmap_1(sK6,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK6))) | v5_pre_topc(X2,sK6,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f25,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0)) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(X2,X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X1,sK5,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,sK5)) & (! [X4] : (r1_tmap_1(X1,sK5,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | v5_pre_topc(X2,X1,sK5)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f29,plain,(
% 1.18/0.99    ((((~r1_tmap_1(sK6,sK5,sK7,sK8) & m1_subset_1(sK8,u1_struct_0(sK6))) | ~v5_pre_topc(sK7,sK6,sK5)) & (! [X4] : (r1_tmap_1(sK6,sK5,sK7,X4) | ~m1_subset_1(X4,u1_struct_0(sK6))) | v5_pre_topc(sK7,sK6,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f28,f27,f26,f25])).
% 1.18/0.99  
% 1.18/0.99  fof(f48,plain,(
% 1.18/0.99    ( ! [X4] : (r1_tmap_1(sK6,sK5,sK7,X4) | ~m1_subset_1(X4,u1_struct_0(sK6)) | v5_pre_topc(sK7,sK6,sK5)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f29])).
% 1.18/0.99  
% 1.18/0.99  fof(f2,axiom,(
% 1.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) => ? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3))))))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f7,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.18/1.00    inference(ennf_transformation,[],[f2])).
% 1.18/1.00  
% 1.18/1.00  fof(f8,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(flattening,[],[f7])).
% 1.18/1.00  
% 1.18/1.00  fof(f16,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(nnf_transformation,[],[f8])).
% 1.18/1.00  
% 1.18/1.00  fof(f17,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (! [X7] : (? [X8] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7) & m1_connsp_2(X8,X0,X6)) | ~m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(rectify,[],[f16])).
% 1.18/1.00  
% 1.18/1.00  fof(f20,plain,(
% 1.18/1.00    ! [X7,X6,X2,X1,X0] : (? [X8] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7) & m1_connsp_2(X8,X0,X6)) => (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7) & m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6)))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f19,plain,(
% 1.18/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) => (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2)) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))) )),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f18,plain,(
% 1.18/1.00    ! [X2,X1,X0] : (? [X3] : (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,sK2(X0,X1,X2))) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f21,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ((! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2)) | ~m1_connsp_2(X5,X0,sK2(X0,X1,X2))) & m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (! [X7] : ((r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7) & m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6)) | ~m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).
% 1.18/1.00  
% 1.18/1.00  fof(f36,plain,(
% 1.18/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  fof(f46,plain,(
% 1.18/1.00    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5))),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f39,plain,(
% 1.18/1.00    ~v2_struct_0(sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f40,plain,(
% 1.18/1.00    v2_pre_topc(sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f41,plain,(
% 1.18/1.00    l1_pre_topc(sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f42,plain,(
% 1.18/1.00    ~v2_struct_0(sK6)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f43,plain,(
% 1.18/1.00    v2_pre_topc(sK6)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f44,plain,(
% 1.18/1.00    l1_pre_topc(sK6)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f45,plain,(
% 1.18/1.00    v1_funct_1(sK7)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f47,plain,(
% 1.18/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f1,axiom,(
% 1.18/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) => ? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3))))))))),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f5,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.18/1.00    inference(ennf_transformation,[],[f1])).
% 1.18/1.00  
% 1.18/1.00  fof(f6,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(flattening,[],[f5])).
% 1.18/1.00  
% 1.18/1.00  fof(f11,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r1_tmap_1(X0,X1,X2,X3) | ? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) & (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~r1_tmap_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(nnf_transformation,[],[f6])).
% 1.18/1.00  
% 1.18/1.00  fof(f12,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r1_tmap_1(X0,X1,X2,X3) | ? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) & (! [X6] : (? [X7] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6) & m1_connsp_2(X7,X0,X3)) | ~m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~r1_tmap_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(rectify,[],[f11])).
% 1.18/1.00  
% 1.18/1.00  fof(f14,plain,(
% 1.18/1.00    ! [X6,X3,X2,X1,X0] : (? [X7] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6) & m1_connsp_2(X7,X0,X3)) => (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6) & m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3)))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f13,plain,(
% 1.18/1.00    ! [X3,X2,X1,X0] : (? [X4] : (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) => (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3)) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f15,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r1_tmap_1(X0,X1,X2,X3) | (! [X5] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3)) | ~m1_connsp_2(X5,X0,X3)) & m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) & (! [X6] : ((r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6) & m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3)) | ~m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~r1_tmap_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).
% 1.18/1.00  
% 1.18/1.00  fof(f30,plain,(
% 1.18/1.00    ( ! [X6,X2,X0,X3,X1] : (m1_connsp_2(sK1(X0,X1,X2,X3,X6),X0,X3) | ~m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f49,plain,(
% 1.18/1.00    m1_subset_1(sK8,u1_struct_0(sK6)) | ~v5_pre_topc(sK7,sK6,sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f34,plain,(
% 1.18/1.00    ( ! [X6,X2,X0,X7,X1] : (m1_connsp_2(sK4(X0,X1,X2,X6,X7),X0,X6) | ~m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  fof(f33,plain,(
% 1.18/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X0,X1,X2,X3) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3)) | ~m1_connsp_2(X5,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f50,plain,(
% 1.18/1.00    ~r1_tmap_1(sK6,sK5,sK7,sK8) | ~v5_pre_topc(sK7,sK6,sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f35,plain,(
% 1.18/1.00    ( ! [X6,X2,X0,X7,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2,X6,X7)),X7) | ~m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  fof(f32,plain,(
% 1.18/1.00    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X0,X1,X2,X3) | m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f38,plain,(
% 1.18/1.00    ( ! [X2,X0,X5,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK3(X0,X1,X2)) | ~m1_connsp_2(X5,X0,sK2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  fof(f31,plain,(
% 1.18/1.00    ( ! [X6,X2,X0,X3,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6) | ~m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f37,plain,(
% 1.18/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_connsp_2(sK3(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  cnf(c_11,negated_conjecture,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_6,plain,
% 1.18/1.00      ( v5_pre_topc(X0,X1,X2)
% 1.18/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.18/1.00      | m1_subset_1(sK2(X1,X2,X0),u1_struct_0(X1))
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | v2_struct_0(X2)
% 1.18/1.00      | ~ v2_pre_topc(X2)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X2)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ v1_funct_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_13,negated_conjecture,
% 1.18/1.00      ( v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK5)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_492,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_subset_1(sK2(sK6,sK5,sK7),u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_6,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_20,negated_conjecture,
% 1.18/1.00      ( ~ v2_struct_0(sK5) ),
% 1.18/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_19,negated_conjecture,
% 1.18/1.00      ( v2_pre_topc(sK5) ),
% 1.18/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_18,negated_conjecture,
% 1.18/1.00      ( l1_pre_topc(sK5) ),
% 1.18/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_17,negated_conjecture,
% 1.18/1.00      ( ~ v2_struct_0(sK6) ),
% 1.18/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_16,negated_conjecture,
% 1.18/1.00      ( v2_pre_topc(sK6) ),
% 1.18/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_15,negated_conjecture,
% 1.18/1.00      ( l1_pre_topc(sK6) ),
% 1.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_14,negated_conjecture,
% 1.18/1.00      ( v1_funct_1(sK7) ),
% 1.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_12,negated_conjecture,
% 1.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
% 1.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_494,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_subset_1(sK2(sK6,sK5,sK7),u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_492,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1256,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_11,c_494]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_3,plain,
% 1.18/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.18/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.18/1.00      | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 1.18/1.00      | m1_connsp_2(sK1(X0,X1,X2,X3,X4),X0,X3)
% 1.18/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.18/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.18/1.00      | v2_struct_0(X0)
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ v2_pre_topc(X0)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X0)
% 1.18/1.00      | ~ v1_funct_1(X2) ),
% 1.18/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_357,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,X0,X1),sK6,X0)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_3,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_361,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,X0,X1),sK6,X0)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_357,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1239,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0),sK6,sK2(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_361,c_494]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1264,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0),sK6,sK2(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(backward_subsumption_resolution,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1256,c_1239]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1633,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0_54,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0_54),sK6,sK2(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_1264]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1668,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
% 1.18/1.00      | ~ m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_10,negated_conjecture,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5) | m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_8,plain,
% 1.18/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 1.18/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.18/1.00      | ~ m1_connsp_2(X3,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X4))
% 1.18/1.00      | m1_connsp_2(sK4(X1,X2,X0,X4,X3),X1,X4)
% 1.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.18/1.00      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | v2_struct_0(X2)
% 1.18/1.00      | ~ v2_pre_topc(X2)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X2)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ v1_funct_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_446,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
% 1.18/1.00      | m1_connsp_2(sK4(sK6,sK5,sK7,X1,X0),sK6,X1)
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_450,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
% 1.18/1.00      | m1_connsp_2(sK4(sK6,sK5,sK7,X1,X0),sK6,X1)
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_446,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1179,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
% 1.18/1.00      | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,X0),sK6,sK8) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_10,c_450]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1634,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0_54,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
% 1.18/1.00      | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,X0_54),sK6,sK8) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_1179]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1665,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
% 1.18/1.00      | ~ m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_0,plain,
% 1.18/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.18/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.18/1.00      | ~ m1_connsp_2(X4,X0,X3)
% 1.18/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.18/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),sK0(X0,X1,X2,X3))
% 1.18/1.00      | v2_struct_0(X0)
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ v2_pre_topc(X0)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X0)
% 1.18/1.00      | ~ v1_funct_1(X2) ),
% 1.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_423,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK6,X0)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_0,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_427,plain,
% 1.18/1.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0))
% 1.18/1.00      | r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK6,X0)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_423,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_428,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK6,X0)
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1),sK0(sK6,sK5,sK7,X0)) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_427]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1132,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,sK8)
% 1.18/1.00      | ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK8)
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_10,c_428]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_9,negated_conjecture,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,sK8) | ~ v5_pre_topc(sK7,sK6,sK5) ),
% 1.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_771,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK8)
% 1.18/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_9,c_428]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_775,plain,
% 1.18/1.00      ( ~ m1_connsp_2(X0,sK6,sK8)
% 1.18/1.00      | ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_771,c_10]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_776,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK8)
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_775]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1135,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK8)
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK0(sK6,sK5,sK7,sK8)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1132,c_776]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_7,plain,
% 1.18/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 1.18/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.18/1.00      | ~ m1_connsp_2(X3,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X4))
% 1.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.18/1.00      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK4(X1,X2,X0,X4,X3)),X3)
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | v2_struct_0(X2)
% 1.18/1.00      | ~ v2_pre_topc(X2)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X2)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ v1_funct_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_469,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0)
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_7,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_473,plain,
% 1.18/1.00      ( r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0)
% 1.18/1.00      | ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_469,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_474,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X1))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,X1,X0)),X0) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_473]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1165,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK4(sK6,sK5,sK7,sK8,X0)),X0) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_10,c_474]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1315,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
% 1.18/1.00      | ~ m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_1135,c_1165]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1,plain,
% 1.18/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.18/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.18/1.00      | m1_connsp_2(sK0(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 1.18/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.18/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.18/1.00      | v2_struct_0(X0)
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ v2_pre_topc(X0)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X0)
% 1.18/1.00      | ~ v1_funct_1(X2) ),
% 1.18/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_403,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | m1_connsp_2(sK0(sK6,sK5,sK7,X0),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_1,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_407,plain,
% 1.18/1.00      ( r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | m1_connsp_2(sK0(sK6,sK5,sK7,X0),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_403,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_791,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
% 1.18/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_9,c_407]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1317,plain,
% 1.18/1.00      ( ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8)
% 1.18/1.00      | ~ v5_pre_topc(sK7,sK6,sK5) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1315,c_10,c_791]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1318,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(sK4(sK6,sK5,sK7,sK8,sK0(sK6,sK5,sK7,sK8)),sK6,sK8) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_1317]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_4,plain,
% 1.18/1.00      ( v5_pre_topc(X0,X1,X2)
% 1.18/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.18/1.00      | ~ m1_connsp_2(X3,X1,sK2(X1,X2,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),sK3(X1,X2,X0))
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | v2_struct_0(X2)
% 1.18/1.00      | ~ v2_pre_topc(X2)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X2)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ v1_funct_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_518,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_522,plain,
% 1.18/1.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7))
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_518,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_523,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK6,sK2(sK6,sK5,sK7))
% 1.18/1.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0),sK3(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_522]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2,plain,
% 1.18/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.18/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.18/1.00      | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 1.18/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.18/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X4)),X4)
% 1.18/1.00      | v2_struct_0(X0)
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ v2_pre_topc(X0)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X0)
% 1.18/1.00      | ~ v1_funct_1(X2) ),
% 1.18/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_380,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1)
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_384,plain,
% 1.18/1.00      ( r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1)
% 1.18/1.00      | ~ r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_380,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_385,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,X0)
% 1.18/1.00      | ~ m1_connsp_2(X1,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,X0))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,X0,X1)),X1) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_384]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1222,plain,
% 1.18/1.00      ( ~ r1_tmap_1(sK6,sK5,sK7,sK2(sK6,sK5,sK7))
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0)),X0) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_385,c_494]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1263,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(X0,sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | r1_tarski(k7_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),X0)),X0) ),
% 1.18/1.00      inference(backward_subsumption_resolution,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1256,c_1222]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1302,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
% 1.18/1.00      | ~ m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_523,c_1263]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_5,plain,
% 1.18/1.00      ( v5_pre_topc(X0,X1,X2)
% 1.18/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.18/1.00      | m1_connsp_2(sK3(X1,X2,X0),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
% 1.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.18/1.00      | v2_struct_0(X1)
% 1.18/1.00      | v2_struct_0(X2)
% 1.18/1.00      | ~ v2_pre_topc(X2)
% 1.18/1.00      | ~ v2_pre_topc(X1)
% 1.18/1.00      | ~ l1_pre_topc(X2)
% 1.18/1.00      | ~ l1_pre_topc(X1)
% 1.18/1.00      | ~ v1_funct_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_505,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7)))
% 1.18/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
% 1.18/1.00      | v2_struct_0(sK5)
% 1.18/1.00      | v2_struct_0(sK6)
% 1.18/1.00      | ~ v2_pre_topc(sK5)
% 1.18/1.00      | ~ v2_pre_topc(sK6)
% 1.18/1.00      | ~ l1_pre_topc(sK5)
% 1.18/1.00      | ~ l1_pre_topc(sK6)
% 1.18/1.00      | ~ v1_funct_1(sK7) ),
% 1.18/1.00      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1304,plain,
% 1.18/1.00      ( ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7))
% 1.18/1.00      | v5_pre_topc(sK7,sK6,sK5) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1302,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12,c_505]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1305,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | ~ m1_connsp_2(sK1(sK6,sK5,sK7,sK2(sK6,sK5,sK7),sK3(sK6,sK5,sK7)),sK6,sK2(sK6,sK5,sK7)) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_1304]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_793,plain,
% 1.18/1.00      ( m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8))
% 1.18/1.00      | ~ v5_pre_topc(sK7,sK6,sK5) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_791,c_10]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_794,plain,
% 1.18/1.00      ( ~ v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK0(sK6,sK5,sK7,sK8),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK8)) ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_793]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_507,plain,
% 1.18/1.00      ( v5_pre_topc(sK7,sK6,sK5)
% 1.18/1.00      | m1_connsp_2(sK3(sK6,sK5,sK7),sK5,k3_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),sK7,sK2(sK6,sK5,sK7))) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_505,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_12]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(contradiction,plain,
% 1.18/1.00      ( $false ),
% 1.18/1.00      inference(minisat,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1668,c_1665,c_1318,c_1305,c_794,c_507]) ).
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  ------                               Statistics
% 1.18/1.00  
% 1.18/1.00  ------ General
% 1.18/1.00  
% 1.18/1.00  abstr_ref_over_cycles:                  0
% 1.18/1.00  abstr_ref_under_cycles:                 0
% 1.18/1.00  gc_basic_clause_elim:                   0
% 1.18/1.00  forced_gc_time:                         0
% 1.18/1.00  parsing_time:                           0.011
% 1.18/1.00  unif_index_cands_time:                  0.
% 1.18/1.00  unif_index_add_time:                    0.
% 1.18/1.00  orderings_time:                         0.
% 1.18/1.00  out_proof_time:                         0.015
% 1.18/1.00  total_time:                             0.091
% 1.18/1.00  num_of_symbols:                         60
% 1.18/1.00  num_of_terms:                           1104
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing
% 1.18/1.00  
% 1.18/1.00  num_of_splits:                          0
% 1.18/1.00  num_of_split_atoms:                     0
% 1.18/1.00  num_of_reused_defs:                     0
% 1.18/1.00  num_eq_ax_congr_red:                    0
% 1.18/1.00  num_of_sem_filtered_clauses:            0
% 1.18/1.00  num_of_subtypes:                        5
% 1.18/1.00  monotx_restored_types:                  0
% 1.18/1.00  sat_num_of_epr_types:                   0
% 1.18/1.00  sat_num_of_non_cyclic_types:            0
% 1.18/1.00  sat_guarded_non_collapsed_types:        0
% 1.18/1.00  num_pure_diseq_elim:                    0
% 1.18/1.00  simp_replaced_by:                       0
% 1.18/1.00  res_preprocessed:                       27
% 1.18/1.00  prep_upred:                             0
% 1.18/1.00  prep_unflattend:                        0
% 1.18/1.00  smt_new_axioms:                         0
% 1.18/1.00  pred_elim_cands:                        2
% 1.18/1.00  pred_elim:                              8
% 1.18/1.00  pred_elim_cl:                           15
% 1.18/1.00  pred_elim_cycles:                       14
% 1.18/1.00  merged_defs:                            0
% 1.18/1.00  merged_defs_ncl:                        0
% 1.18/1.00  bin_hyper_res:                          0
% 1.18/1.00  prep_cycles:                            2
% 1.18/1.00  pred_elim_time:                         0.031
% 1.18/1.00  splitting_time:                         0.
% 1.18/1.00  sem_filter_time:                        0.
% 1.18/1.00  monotx_time:                            0.
% 1.18/1.00  subtype_inf_time:                       0.
% 1.18/1.00  
% 1.18/1.00  ------ Problem properties
% 1.18/1.00  
% 1.18/1.00  clauses:                                6
% 1.18/1.00  conjectures:                            0
% 1.18/1.00  epr:                                    0
% 1.18/1.00  horn:                                   4
% 1.18/1.00  ground:                                 4
% 1.18/1.00  unary:                                  0
% 1.18/1.00  binary:                                 4
% 1.18/1.00  lits:                                   14
% 1.18/1.00  lits_eq:                                0
% 1.18/1.00  fd_pure:                                0
% 1.18/1.00  fd_pseudo:                              0
% 1.18/1.00  fd_cond:                                0
% 1.18/1.00  fd_pseudo_cond:                         0
% 1.18/1.00  ac_symbols:                             0
% 1.18/1.00  
% 1.18/1.00  ------ Propositional Solver
% 1.18/1.00  
% 1.18/1.00  prop_solver_calls:                      13
% 1.18/1.00  prop_fast_solver_calls:                 671
% 1.18/1.00  smt_solver_calls:                       0
% 1.18/1.00  smt_fast_solver_calls:                  0
% 1.18/1.00  prop_num_of_clauses:                    327
% 1.18/1.00  prop_preprocess_simplified:             989
% 1.18/1.00  prop_fo_subsumed:                       80
% 1.18/1.00  prop_solver_time:                       0.
% 1.18/1.00  smt_solver_time:                        0.
% 1.18/1.00  smt_fast_solver_time:                   0.
% 1.18/1.00  prop_fast_solver_time:                  0.
% 1.18/1.00  prop_unsat_core_time:                   0.
% 1.18/1.00  
% 1.18/1.00  ------ QBF
% 1.18/1.00  
% 1.18/1.00  qbf_q_res:                              0
% 1.18/1.00  qbf_num_tautologies:                    0
% 1.18/1.00  qbf_prep_cycles:                        0
% 1.18/1.00  
% 1.18/1.00  ------ BMC1
% 1.18/1.00  
% 1.18/1.00  bmc1_current_bound:                     -1
% 1.18/1.00  bmc1_last_solved_bound:                 -1
% 1.18/1.00  bmc1_unsat_core_size:                   -1
% 1.18/1.00  bmc1_unsat_core_parents_size:           -1
% 1.18/1.00  bmc1_merge_next_fun:                    0
% 1.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation
% 1.18/1.00  
% 1.18/1.00  inst_num_of_clauses:                    7
% 1.18/1.00  inst_num_in_passive:                    0
% 1.18/1.00  inst_num_in_active:                     6
% 1.18/1.00  inst_num_in_unprocessed:                0
% 1.18/1.00  inst_num_of_loops:                      11
% 1.18/1.00  inst_num_of_learning_restarts:          0
% 1.18/1.00  inst_num_moves_active_passive:          3
% 1.18/1.00  inst_lit_activity:                      0
% 1.18/1.00  inst_lit_activity_moves:                0
% 1.18/1.00  inst_num_tautologies:                   0
% 1.18/1.00  inst_num_prop_implied:                  0
% 1.18/1.00  inst_num_existing_simplified:           0
% 1.18/1.00  inst_num_eq_res_simplified:             0
% 1.18/1.00  inst_num_child_elim:                    0
% 1.18/1.00  inst_num_of_dismatching_blockings:      0
% 1.18/1.00  inst_num_of_non_proper_insts:           2
% 1.18/1.00  inst_num_of_duplicates:                 0
% 1.18/1.00  inst_inst_num_from_inst_to_res:         0
% 1.18/1.00  inst_dismatching_checking_time:         0.
% 1.18/1.00  
% 1.18/1.00  ------ Resolution
% 1.18/1.00  
% 1.18/1.00  res_num_of_clauses:                     0
% 1.18/1.00  res_num_in_passive:                     0
% 1.18/1.00  res_num_in_active:                      0
% 1.18/1.00  res_num_of_loops:                       29
% 1.18/1.00  res_forward_subset_subsumed:            2
% 1.18/1.00  res_backward_subset_subsumed:           2
% 1.18/1.00  res_forward_subsumed:                   0
% 1.18/1.00  res_backward_subsumed:                  0
% 1.18/1.00  res_forward_subsumption_resolution:     0
% 1.18/1.00  res_backward_subsumption_resolution:    2
% 1.18/1.00  res_clause_to_clause_subsumption:       5
% 1.18/1.00  res_orphan_elimination:                 0
% 1.18/1.00  res_tautology_del:                      8
% 1.18/1.00  res_num_eq_res_simplified:              0
% 1.18/1.00  res_num_sel_changes:                    0
% 1.18/1.00  res_moves_from_active_to_pass:          0
% 1.18/1.00  
% 1.18/1.00  ------ Superposition
% 1.18/1.00  
% 1.18/1.00  sup_time_total:                         0.
% 1.18/1.00  sup_time_generating:                    0.
% 1.18/1.00  sup_time_sim_full:                      0.
% 1.18/1.00  sup_time_sim_immed:                     0.
% 1.18/1.00  
% 1.18/1.00  sup_num_of_clauses:                     0
% 1.18/1.00  sup_num_in_active:                      0
% 1.18/1.00  sup_num_in_passive:                     0
% 1.18/1.00  sup_num_of_loops:                       0
% 1.18/1.00  sup_fw_superposition:                   0
% 1.18/1.00  sup_bw_superposition:                   0
% 1.18/1.00  sup_immediate_simplified:               0
% 1.18/1.00  sup_given_eliminated:                   0
% 1.18/1.00  comparisons_done:                       0
% 1.18/1.00  comparisons_avoided:                    0
% 1.18/1.00  
% 1.18/1.00  ------ Simplifications
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  sim_fw_subset_subsumed:                 0
% 1.18/1.00  sim_bw_subset_subsumed:                 0
% 1.18/1.00  sim_fw_subsumed:                        0
% 1.18/1.00  sim_bw_subsumed:                        0
% 1.18/1.00  sim_fw_subsumption_res:                 0
% 1.18/1.00  sim_bw_subsumption_res:                 0
% 1.18/1.00  sim_tautology_del:                      0
% 1.18/1.00  sim_eq_tautology_del:                   0
% 1.18/1.00  sim_eq_res_simp:                        0
% 1.18/1.00  sim_fw_demodulated:                     0
% 1.18/1.00  sim_bw_demodulated:                     0
% 1.18/1.00  sim_light_normalised:                   0
% 1.18/1.00  sim_joinable_taut:                      0
% 1.18/1.00  sim_joinable_simp:                      0
% 1.18/1.00  sim_ac_normalised:                      0
% 1.18/1.00  sim_smt_subsumption:                    0
% 1.18/1.00  
%------------------------------------------------------------------------------
