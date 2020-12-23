%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:45 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 789 expanded)
%              Number of clauses        :   97 ( 126 expanded)
%              Number of leaves         :   18 ( 315 expanded)
%              Depth                    :   40
%              Number of atoms          : 1340 (12728 expanded)
%              Number of equality atoms :  114 ( 918 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK5 = X4
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | ~ r1_tmap_1(X1,X0,X2,X4) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | r1_tmap_1(X1,X0,X2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | ~ r1_tmap_1(X1,X0,X2,sK4) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK4) )
            & sK4 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | ~ r1_tmap_1(X1,X0,X2,X4) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | r1_tmap_1(X1,X0,X2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_pre_topc(X3,X1)
          & v1_tsep_1(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK3,X1)
        & v1_tsep_1(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | ~ r1_tmap_1(X1,X0,X2,X4) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | r1_tmap_1(X1,X0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_pre_topc(X3,X1)
              & v1_tsep_1(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK2,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | r1_tmap_1(X1,X0,sK2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK1,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | r1_tmap_1(sK1,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_pre_topc(X3,sK1)
                & v1_tsep_1(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
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
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42,f41,f40])).

fof(f74,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f10,axiom,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_411,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_964,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_965,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_967,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_27])).

cnf(c_1279,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_967])).

cnf(c_1280,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1279])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1282,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1280,c_23])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_178,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_179,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_22,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_494,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_22])).

cnf(c_495,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_497,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_28,c_27,c_21])).

cnf(c_507,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_497])).

cnf(c_508,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_512,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_29,c_28,c_27])).

cnf(c_513,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_512])).

cnf(c_536,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X2)
    | X0 != X1
    | u1_struct_0(sK3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_513])).

cnf(c_537,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_596,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(sK1))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | X6 != X3
    | u1_struct_0(sK3) != X5
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_537])).

cnf(c_597,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_601,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_29,c_28,c_27])).

cnf(c_602,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_601])).

cnf(c_820,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_602])).

cnf(c_821,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_825,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_26])).

cnf(c_826,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_825])).

cnf(c_1014,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_826])).

cnf(c_1015,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_935,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_936,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_1019,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_27,c_23,c_936])).

cnf(c_1020,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1019])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK1 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_947,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_951,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_29,c_27,c_23])).

cnf(c_952,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_951])).

cnf(c_1036,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1020,c_952])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1047,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1036,c_1])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1182,plain,
    ( r1_tmap_1(sK1,X0,sK2,X1)
    | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1047,c_31])).

cnf(c_1183,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1182])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | r1_tmap_1(sK1,sK0,sK2,X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_32,c_30,c_24])).

cnf(c_1188,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1187])).

cnf(c_1296,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1282,c_1188])).

cnf(c_1317,plain,
    ( r1_tmap_1(sK1,sK0,sK2,X0)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1296])).

cnf(c_1940,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_15,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_13])).

cnf(c_171,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_714,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_25])).

cnf(c_715,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_719,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_26])).

cnf(c_720,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_755,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_720,c_7])).

cnf(c_975,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK1 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_755])).

cnf(c_976,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_980,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_29,c_28,c_27,c_23])).

cnf(c_981,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_980])).

cnf(c_1209,plain,
    ( ~ r1_tmap_1(sK1,X0,sK2,X1)
    | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_981,c_31])).

cnf(c_1210,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1209])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_32,c_30,c_24])).

cnf(c_1215,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_1214])).

cnf(c_1322,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1215])).

cnf(c_1937,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1823,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1854,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1823,c_18])).

cnf(c_1905,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1854])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1822,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1849,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1822,c_18])).

cnf(c_1899,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1849])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1940,c_1937,c_1905,c_1899,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.48/0.99  
% 1.48/0.99  ------  iProver source info
% 1.48/0.99  
% 1.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.48/0.99  git: non_committed_changes: false
% 1.48/0.99  git: last_make_outside_of_git: false
% 1.48/0.99  
% 1.48/0.99  ------ 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options
% 1.48/0.99  
% 1.48/0.99  --out_options                           all
% 1.48/0.99  --tptp_safe_out                         true
% 1.48/0.99  --problem_path                          ""
% 1.48/0.99  --include_path                          ""
% 1.48/0.99  --clausifier                            res/vclausify_rel
% 1.48/0.99  --clausifier_options                    --mode clausify
% 1.48/0.99  --stdin                                 false
% 1.48/0.99  --stats_out                             all
% 1.48/0.99  
% 1.48/0.99  ------ General Options
% 1.48/0.99  
% 1.48/0.99  --fof                                   false
% 1.48/0.99  --time_out_real                         305.
% 1.48/0.99  --time_out_virtual                      -1.
% 1.48/0.99  --symbol_type_check                     false
% 1.48/0.99  --clausify_out                          false
% 1.48/0.99  --sig_cnt_out                           false
% 1.48/0.99  --trig_cnt_out                          false
% 1.48/0.99  --trig_cnt_out_tolerance                1.
% 1.48/0.99  --trig_cnt_out_sk_spl                   false
% 1.48/0.99  --abstr_cl_out                          false
% 1.48/0.99  
% 1.48/0.99  ------ Global Options
% 1.48/0.99  
% 1.48/0.99  --schedule                              default
% 1.48/0.99  --add_important_lit                     false
% 1.48/0.99  --prop_solver_per_cl                    1000
% 1.48/0.99  --min_unsat_core                        false
% 1.48/0.99  --soft_assumptions                      false
% 1.48/0.99  --soft_lemma_size                       3
% 1.48/0.99  --prop_impl_unit_size                   0
% 1.48/0.99  --prop_impl_unit                        []
% 1.48/0.99  --share_sel_clauses                     true
% 1.48/0.99  --reset_solvers                         false
% 1.48/0.99  --bc_imp_inh                            [conj_cone]
% 1.48/0.99  --conj_cone_tolerance                   3.
% 1.48/0.99  --extra_neg_conj                        none
% 1.48/0.99  --large_theory_mode                     true
% 1.48/0.99  --prolific_symb_bound                   200
% 1.48/0.99  --lt_threshold                          2000
% 1.48/0.99  --clause_weak_htbl                      true
% 1.48/0.99  --gc_record_bc_elim                     false
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing Options
% 1.48/0.99  
% 1.48/0.99  --preprocessing_flag                    true
% 1.48/0.99  --time_out_prep_mult                    0.1
% 1.48/0.99  --splitting_mode                        input
% 1.48/0.99  --splitting_grd                         true
% 1.48/0.99  --splitting_cvd                         false
% 1.48/0.99  --splitting_cvd_svl                     false
% 1.48/0.99  --splitting_nvd                         32
% 1.48/0.99  --sub_typing                            true
% 1.48/0.99  --prep_gs_sim                           true
% 1.48/0.99  --prep_unflatten                        true
% 1.48/0.99  --prep_res_sim                          true
% 1.48/0.99  --prep_upred                            true
% 1.48/0.99  --prep_sem_filter                       exhaustive
% 1.48/0.99  --prep_sem_filter_out                   false
% 1.48/0.99  --pred_elim                             true
% 1.48/0.99  --res_sim_input                         true
% 1.48/0.99  --eq_ax_congr_red                       true
% 1.48/0.99  --pure_diseq_elim                       true
% 1.48/0.99  --brand_transform                       false
% 1.48/0.99  --non_eq_to_eq                          false
% 1.48/0.99  --prep_def_merge                        true
% 1.48/0.99  --prep_def_merge_prop_impl              false
% 1.48/0.99  --prep_def_merge_mbd                    true
% 1.48/0.99  --prep_def_merge_tr_red                 false
% 1.48/0.99  --prep_def_merge_tr_cl                  false
% 1.48/0.99  --smt_preprocessing                     true
% 1.48/0.99  --smt_ac_axioms                         fast
% 1.48/0.99  --preprocessed_out                      false
% 1.48/0.99  --preprocessed_stats                    false
% 1.48/0.99  
% 1.48/0.99  ------ Abstraction refinement Options
% 1.48/0.99  
% 1.48/0.99  --abstr_ref                             []
% 1.48/0.99  --abstr_ref_prep                        false
% 1.48/0.99  --abstr_ref_until_sat                   false
% 1.48/0.99  --abstr_ref_sig_restrict                funpre
% 1.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/0.99  --abstr_ref_under                       []
% 1.48/0.99  
% 1.48/0.99  ------ SAT Options
% 1.48/0.99  
% 1.48/0.99  --sat_mode                              false
% 1.48/0.99  --sat_fm_restart_options                ""
% 1.48/0.99  --sat_gr_def                            false
% 1.48/0.99  --sat_epr_types                         true
% 1.48/0.99  --sat_non_cyclic_types                  false
% 1.48/0.99  --sat_finite_models                     false
% 1.48/0.99  --sat_fm_lemmas                         false
% 1.48/0.99  --sat_fm_prep                           false
% 1.48/0.99  --sat_fm_uc_incr                        true
% 1.48/0.99  --sat_out_model                         small
% 1.48/0.99  --sat_out_clauses                       false
% 1.48/0.99  
% 1.48/0.99  ------ QBF Options
% 1.48/0.99  
% 1.48/0.99  --qbf_mode                              false
% 1.48/0.99  --qbf_elim_univ                         false
% 1.48/0.99  --qbf_dom_inst                          none
% 1.48/0.99  --qbf_dom_pre_inst                      false
% 1.48/0.99  --qbf_sk_in                             false
% 1.48/0.99  --qbf_pred_elim                         true
% 1.48/0.99  --qbf_split                             512
% 1.48/0.99  
% 1.48/0.99  ------ BMC1 Options
% 1.48/0.99  
% 1.48/0.99  --bmc1_incremental                      false
% 1.48/0.99  --bmc1_axioms                           reachable_all
% 1.48/0.99  --bmc1_min_bound                        0
% 1.48/0.99  --bmc1_max_bound                        -1
% 1.48/0.99  --bmc1_max_bound_default                -1
% 1.48/0.99  --bmc1_symbol_reachability              true
% 1.48/0.99  --bmc1_property_lemmas                  false
% 1.48/0.99  --bmc1_k_induction                      false
% 1.48/0.99  --bmc1_non_equiv_states                 false
% 1.48/0.99  --bmc1_deadlock                         false
% 1.48/0.99  --bmc1_ucm                              false
% 1.48/0.99  --bmc1_add_unsat_core                   none
% 1.48/0.99  --bmc1_unsat_core_children              false
% 1.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/0.99  --bmc1_out_stat                         full
% 1.48/0.99  --bmc1_ground_init                      false
% 1.48/0.99  --bmc1_pre_inst_next_state              false
% 1.48/0.99  --bmc1_pre_inst_state                   false
% 1.48/0.99  --bmc1_pre_inst_reach_state             false
% 1.48/0.99  --bmc1_out_unsat_core                   false
% 1.48/0.99  --bmc1_aig_witness_out                  false
% 1.48/0.99  --bmc1_verbose                          false
% 1.48/0.99  --bmc1_dump_clauses_tptp                false
% 1.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.48/0.99  --bmc1_dump_file                        -
% 1.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.48/0.99  --bmc1_ucm_extend_mode                  1
% 1.48/0.99  --bmc1_ucm_init_mode                    2
% 1.48/0.99  --bmc1_ucm_cone_mode                    none
% 1.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.48/0.99  --bmc1_ucm_relax_model                  4
% 1.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/0.99  --bmc1_ucm_layered_model                none
% 1.48/0.99  --bmc1_ucm_max_lemma_size               10
% 1.48/0.99  
% 1.48/0.99  ------ AIG Options
% 1.48/0.99  
% 1.48/0.99  --aig_mode                              false
% 1.48/0.99  
% 1.48/0.99  ------ Instantiation Options
% 1.48/0.99  
% 1.48/0.99  --instantiation_flag                    true
% 1.48/0.99  --inst_sos_flag                         false
% 1.48/0.99  --inst_sos_phase                        true
% 1.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel_side                     num_symb
% 1.48/0.99  --inst_solver_per_active                1400
% 1.48/0.99  --inst_solver_calls_frac                1.
% 1.48/0.99  --inst_passive_queue_type               priority_queues
% 1.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/0.99  --inst_passive_queues_freq              [25;2]
% 1.48/0.99  --inst_dismatching                      true
% 1.48/0.99  --inst_eager_unprocessed_to_passive     true
% 1.48/0.99  --inst_prop_sim_given                   true
% 1.48/0.99  --inst_prop_sim_new                     false
% 1.48/0.99  --inst_subs_new                         false
% 1.48/0.99  --inst_eq_res_simp                      false
% 1.48/0.99  --inst_subs_given                       false
% 1.48/0.99  --inst_orphan_elimination               true
% 1.48/0.99  --inst_learning_loop_flag               true
% 1.48/0.99  --inst_learning_start                   3000
% 1.48/0.99  --inst_learning_factor                  2
% 1.48/0.99  --inst_start_prop_sim_after_learn       3
% 1.48/0.99  --inst_sel_renew                        solver
% 1.48/0.99  --inst_lit_activity_flag                true
% 1.48/0.99  --inst_restr_to_given                   false
% 1.48/0.99  --inst_activity_threshold               500
% 1.48/0.99  --inst_out_proof                        true
% 1.48/0.99  
% 1.48/0.99  ------ Resolution Options
% 1.48/0.99  
% 1.48/0.99  --resolution_flag                       true
% 1.48/0.99  --res_lit_sel                           adaptive
% 1.48/0.99  --res_lit_sel_side                      none
% 1.48/0.99  --res_ordering                          kbo
% 1.48/0.99  --res_to_prop_solver                    active
% 1.48/0.99  --res_prop_simpl_new                    false
% 1.48/0.99  --res_prop_simpl_given                  true
% 1.48/0.99  --res_passive_queue_type                priority_queues
% 1.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/0.99  --res_passive_queues_freq               [15;5]
% 1.48/0.99  --res_forward_subs                      full
% 1.48/0.99  --res_backward_subs                     full
% 1.48/0.99  --res_forward_subs_resolution           true
% 1.48/0.99  --res_backward_subs_resolution          true
% 1.48/0.99  --res_orphan_elimination                true
% 1.48/0.99  --res_time_limit                        2.
% 1.48/0.99  --res_out_proof                         true
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Options
% 1.48/0.99  
% 1.48/0.99  --superposition_flag                    true
% 1.48/0.99  --sup_passive_queue_type                priority_queues
% 1.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.48/0.99  --demod_completeness_check              fast
% 1.48/0.99  --demod_use_ground                      true
% 1.48/0.99  --sup_to_prop_solver                    passive
% 1.48/0.99  --sup_prop_simpl_new                    true
% 1.48/0.99  --sup_prop_simpl_given                  true
% 1.48/0.99  --sup_fun_splitting                     false
% 1.48/0.99  --sup_smt_interval                      50000
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Simplification Setup
% 1.48/0.99  
% 1.48/0.99  --sup_indices_passive                   []
% 1.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_full_bw                           [BwDemod]
% 1.48/0.99  --sup_immed_triv                        [TrivRules]
% 1.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_immed_bw_main                     []
% 1.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  
% 1.48/0.99  ------ Combination Options
% 1.48/0.99  
% 1.48/0.99  --comb_res_mult                         3
% 1.48/0.99  --comb_sup_mult                         2
% 1.48/0.99  --comb_inst_mult                        10
% 1.48/0.99  
% 1.48/0.99  ------ Debug Options
% 1.48/0.99  
% 1.48/0.99  --dbg_backtrace                         false
% 1.48/0.99  --dbg_dump_prop_clauses                 false
% 1.48/0.99  --dbg_dump_prop_clauses_file            -
% 1.48/0.99  --dbg_out_stat                          false
% 1.48/0.99  ------ Parsing...
% 1.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.48/0.99  ------ Proving...
% 1.48/0.99  ------ Problem Properties 
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  clauses                                 16
% 1.48/0.99  conjectures                             6
% 1.48/0.99  EPR                                     3
% 1.48/0.99  Horn                                    15
% 1.48/0.99  unary                                   6
% 1.48/0.99  binary                                  3
% 1.48/0.99  lits                                    35
% 1.48/0.99  lits eq                                 4
% 1.48/0.99  fd_pure                                 0
% 1.48/0.99  fd_pseudo                               0
% 1.48/0.99  fd_cond                                 0
% 1.48/0.99  fd_pseudo_cond                          1
% 1.48/0.99  AC symbols                              0
% 1.48/0.99  
% 1.48/0.99  ------ Schedule dynamic 5 is on 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  ------ 
% 1.48/0.99  Current options:
% 1.48/0.99  ------ 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options
% 1.48/0.99  
% 1.48/0.99  --out_options                           all
% 1.48/0.99  --tptp_safe_out                         true
% 1.48/0.99  --problem_path                          ""
% 1.48/0.99  --include_path                          ""
% 1.48/0.99  --clausifier                            res/vclausify_rel
% 1.48/0.99  --clausifier_options                    --mode clausify
% 1.48/0.99  --stdin                                 false
% 1.48/0.99  --stats_out                             all
% 1.48/0.99  
% 1.48/0.99  ------ General Options
% 1.48/0.99  
% 1.48/0.99  --fof                                   false
% 1.48/0.99  --time_out_real                         305.
% 1.48/0.99  --time_out_virtual                      -1.
% 1.48/0.99  --symbol_type_check                     false
% 1.48/0.99  --clausify_out                          false
% 1.48/0.99  --sig_cnt_out                           false
% 1.48/0.99  --trig_cnt_out                          false
% 1.48/0.99  --trig_cnt_out_tolerance                1.
% 1.48/0.99  --trig_cnt_out_sk_spl                   false
% 1.48/0.99  --abstr_cl_out                          false
% 1.48/0.99  
% 1.48/0.99  ------ Global Options
% 1.48/0.99  
% 1.48/0.99  --schedule                              default
% 1.48/0.99  --add_important_lit                     false
% 1.48/0.99  --prop_solver_per_cl                    1000
% 1.48/0.99  --min_unsat_core                        false
% 1.48/0.99  --soft_assumptions                      false
% 1.48/0.99  --soft_lemma_size                       3
% 1.48/0.99  --prop_impl_unit_size                   0
% 1.48/0.99  --prop_impl_unit                        []
% 1.48/0.99  --share_sel_clauses                     true
% 1.48/0.99  --reset_solvers                         false
% 1.48/0.99  --bc_imp_inh                            [conj_cone]
% 1.48/0.99  --conj_cone_tolerance                   3.
% 1.48/0.99  --extra_neg_conj                        none
% 1.48/0.99  --large_theory_mode                     true
% 1.48/0.99  --prolific_symb_bound                   200
% 1.48/0.99  --lt_threshold                          2000
% 1.48/0.99  --clause_weak_htbl                      true
% 1.48/0.99  --gc_record_bc_elim                     false
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing Options
% 1.48/0.99  
% 1.48/0.99  --preprocessing_flag                    true
% 1.48/0.99  --time_out_prep_mult                    0.1
% 1.48/0.99  --splitting_mode                        input
% 1.48/0.99  --splitting_grd                         true
% 1.48/0.99  --splitting_cvd                         false
% 1.48/0.99  --splitting_cvd_svl                     false
% 1.48/0.99  --splitting_nvd                         32
% 1.48/0.99  --sub_typing                            true
% 1.48/0.99  --prep_gs_sim                           true
% 1.48/0.99  --prep_unflatten                        true
% 1.48/0.99  --prep_res_sim                          true
% 1.48/0.99  --prep_upred                            true
% 1.48/0.99  --prep_sem_filter                       exhaustive
% 1.48/0.99  --prep_sem_filter_out                   false
% 1.48/0.99  --pred_elim                             true
% 1.48/0.99  --res_sim_input                         true
% 1.48/0.99  --eq_ax_congr_red                       true
% 1.48/0.99  --pure_diseq_elim                       true
% 1.48/0.99  --brand_transform                       false
% 1.48/0.99  --non_eq_to_eq                          false
% 1.48/0.99  --prep_def_merge                        true
% 1.48/0.99  --prep_def_merge_prop_impl              false
% 1.48/0.99  --prep_def_merge_mbd                    true
% 1.48/0.99  --prep_def_merge_tr_red                 false
% 1.48/0.99  --prep_def_merge_tr_cl                  false
% 1.48/0.99  --smt_preprocessing                     true
% 1.48/0.99  --smt_ac_axioms                         fast
% 1.48/0.99  --preprocessed_out                      false
% 1.48/0.99  --preprocessed_stats                    false
% 1.48/0.99  
% 1.48/0.99  ------ Abstraction refinement Options
% 1.48/0.99  
% 1.48/0.99  --abstr_ref                             []
% 1.48/0.99  --abstr_ref_prep                        false
% 1.48/0.99  --abstr_ref_until_sat                   false
% 1.48/0.99  --abstr_ref_sig_restrict                funpre
% 1.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/0.99  --abstr_ref_under                       []
% 1.48/0.99  
% 1.48/0.99  ------ SAT Options
% 1.48/0.99  
% 1.48/0.99  --sat_mode                              false
% 1.48/0.99  --sat_fm_restart_options                ""
% 1.48/0.99  --sat_gr_def                            false
% 1.48/0.99  --sat_epr_types                         true
% 1.48/0.99  --sat_non_cyclic_types                  false
% 1.48/0.99  --sat_finite_models                     false
% 1.48/0.99  --sat_fm_lemmas                         false
% 1.48/0.99  --sat_fm_prep                           false
% 1.48/0.99  --sat_fm_uc_incr                        true
% 1.48/0.99  --sat_out_model                         small
% 1.48/0.99  --sat_out_clauses                       false
% 1.48/0.99  
% 1.48/0.99  ------ QBF Options
% 1.48/0.99  
% 1.48/0.99  --qbf_mode                              false
% 1.48/0.99  --qbf_elim_univ                         false
% 1.48/0.99  --qbf_dom_inst                          none
% 1.48/0.99  --qbf_dom_pre_inst                      false
% 1.48/0.99  --qbf_sk_in                             false
% 1.48/0.99  --qbf_pred_elim                         true
% 1.48/0.99  --qbf_split                             512
% 1.48/0.99  
% 1.48/0.99  ------ BMC1 Options
% 1.48/0.99  
% 1.48/0.99  --bmc1_incremental                      false
% 1.48/0.99  --bmc1_axioms                           reachable_all
% 1.48/0.99  --bmc1_min_bound                        0
% 1.48/0.99  --bmc1_max_bound                        -1
% 1.48/0.99  --bmc1_max_bound_default                -1
% 1.48/0.99  --bmc1_symbol_reachability              true
% 1.48/0.99  --bmc1_property_lemmas                  false
% 1.48/0.99  --bmc1_k_induction                      false
% 1.48/0.99  --bmc1_non_equiv_states                 false
% 1.48/0.99  --bmc1_deadlock                         false
% 1.48/0.99  --bmc1_ucm                              false
% 1.48/0.99  --bmc1_add_unsat_core                   none
% 1.48/0.99  --bmc1_unsat_core_children              false
% 1.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/0.99  --bmc1_out_stat                         full
% 1.48/0.99  --bmc1_ground_init                      false
% 1.48/0.99  --bmc1_pre_inst_next_state              false
% 1.48/0.99  --bmc1_pre_inst_state                   false
% 1.48/0.99  --bmc1_pre_inst_reach_state             false
% 1.48/0.99  --bmc1_out_unsat_core                   false
% 1.48/0.99  --bmc1_aig_witness_out                  false
% 1.48/0.99  --bmc1_verbose                          false
% 1.48/0.99  --bmc1_dump_clauses_tptp                false
% 1.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.48/0.99  --bmc1_dump_file                        -
% 1.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.48/0.99  --bmc1_ucm_extend_mode                  1
% 1.48/0.99  --bmc1_ucm_init_mode                    2
% 1.48/0.99  --bmc1_ucm_cone_mode                    none
% 1.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.48/0.99  --bmc1_ucm_relax_model                  4
% 1.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/0.99  --bmc1_ucm_layered_model                none
% 1.48/0.99  --bmc1_ucm_max_lemma_size               10
% 1.48/0.99  
% 1.48/0.99  ------ AIG Options
% 1.48/0.99  
% 1.48/0.99  --aig_mode                              false
% 1.48/0.99  
% 1.48/0.99  ------ Instantiation Options
% 1.48/0.99  
% 1.48/0.99  --instantiation_flag                    true
% 1.48/0.99  --inst_sos_flag                         false
% 1.48/0.99  --inst_sos_phase                        true
% 1.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel_side                     none
% 1.48/0.99  --inst_solver_per_active                1400
% 1.48/0.99  --inst_solver_calls_frac                1.
% 1.48/0.99  --inst_passive_queue_type               priority_queues
% 1.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/0.99  --inst_passive_queues_freq              [25;2]
% 1.48/0.99  --inst_dismatching                      true
% 1.48/0.99  --inst_eager_unprocessed_to_passive     true
% 1.48/0.99  --inst_prop_sim_given                   true
% 1.48/0.99  --inst_prop_sim_new                     false
% 1.48/0.99  --inst_subs_new                         false
% 1.48/0.99  --inst_eq_res_simp                      false
% 1.48/0.99  --inst_subs_given                       false
% 1.48/0.99  --inst_orphan_elimination               true
% 1.48/0.99  --inst_learning_loop_flag               true
% 1.48/0.99  --inst_learning_start                   3000
% 1.48/0.99  --inst_learning_factor                  2
% 1.48/0.99  --inst_start_prop_sim_after_learn       3
% 1.48/0.99  --inst_sel_renew                        solver
% 1.48/0.99  --inst_lit_activity_flag                true
% 1.48/0.99  --inst_restr_to_given                   false
% 1.48/0.99  --inst_activity_threshold               500
% 1.48/0.99  --inst_out_proof                        true
% 1.48/0.99  
% 1.48/0.99  ------ Resolution Options
% 1.48/0.99  
% 1.48/0.99  --resolution_flag                       false
% 1.48/0.99  --res_lit_sel                           adaptive
% 1.48/0.99  --res_lit_sel_side                      none
% 1.48/0.99  --res_ordering                          kbo
% 1.48/0.99  --res_to_prop_solver                    active
% 1.48/0.99  --res_prop_simpl_new                    false
% 1.48/0.99  --res_prop_simpl_given                  true
% 1.48/0.99  --res_passive_queue_type                priority_queues
% 1.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/0.99  --res_passive_queues_freq               [15;5]
% 1.48/0.99  --res_forward_subs                      full
% 1.48/0.99  --res_backward_subs                     full
% 1.48/0.99  --res_forward_subs_resolution           true
% 1.48/0.99  --res_backward_subs_resolution          true
% 1.48/0.99  --res_orphan_elimination                true
% 1.48/0.99  --res_time_limit                        2.
% 1.48/0.99  --res_out_proof                         true
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Options
% 1.48/0.99  
% 1.48/0.99  --superposition_flag                    true
% 1.48/0.99  --sup_passive_queue_type                priority_queues
% 1.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.48/0.99  --demod_completeness_check              fast
% 1.48/0.99  --demod_use_ground                      true
% 1.48/0.99  --sup_to_prop_solver                    passive
% 1.48/0.99  --sup_prop_simpl_new                    true
% 1.48/0.99  --sup_prop_simpl_given                  true
% 1.48/0.99  --sup_fun_splitting                     false
% 1.48/0.99  --sup_smt_interval                      50000
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Simplification Setup
% 1.48/0.99  
% 1.48/0.99  --sup_indices_passive                   []
% 1.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_full_bw                           [BwDemod]
% 1.48/0.99  --sup_immed_triv                        [TrivRules]
% 1.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_immed_bw_main                     []
% 1.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  
% 1.48/0.99  ------ Combination Options
% 1.48/0.99  
% 1.48/0.99  --comb_res_mult                         3
% 1.48/0.99  --comb_sup_mult                         2
% 1.48/0.99  --comb_inst_mult                        10
% 1.48/0.99  
% 1.48/0.99  ------ Debug Options
% 1.48/0.99  
% 1.48/0.99  --dbg_backtrace                         false
% 1.48/0.99  --dbg_dump_prop_clauses                 false
% 1.48/0.99  --dbg_dump_prop_clauses_file            -
% 1.48/0.99  --dbg_out_stat                          false
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  ------ Proving...
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  % SZS status Theorem for theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  fof(f3,axiom,(
% 1.48/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f16,plain,(
% 1.48/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.48/0.99    inference(ennf_transformation,[],[f3])).
% 1.48/0.99  
% 1.48/0.99  fof(f51,plain,(
% 1.48/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f16])).
% 1.48/0.99  
% 1.48/0.99  fof(f5,axiom,(
% 1.48/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f18,plain,(
% 1.48/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f5])).
% 1.48/0.99  
% 1.48/0.99  fof(f19,plain,(
% 1.48/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f18])).
% 1.48/0.99  
% 1.48/0.99  fof(f53,plain,(
% 1.48/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f19])).
% 1.48/0.99  
% 1.48/0.99  fof(f4,axiom,(
% 1.48/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f17,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.99    inference(ennf_transformation,[],[f4])).
% 1.48/0.99  
% 1.48/0.99  fof(f52,plain,(
% 1.48/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f17])).
% 1.48/0.99  
% 1.48/0.99  fof(f12,conjecture,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f13,negated_conjecture,(
% 1.48/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.48/0.99    inference(negated_conjecture,[],[f12])).
% 1.48/0.99  
% 1.48/0.99  fof(f31,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f13])).
% 1.48/0.99  
% 1.48/0.99  fof(f32,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f31])).
% 1.48/0.99  
% 1.48/0.99  fof(f38,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f32])).
% 1.48/0.99  
% 1.48/0.99  fof(f39,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f45,plain,(
% 1.48/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f44,plain,(
% 1.48/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f43,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f42,plain,(
% 1.48/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f41,plain,(
% 1.48/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f40,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f46,plain,(
% 1.48/0.99    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42,f41,f40])).
% 1.48/0.99  
% 1.48/0.99  fof(f74,plain,(
% 1.48/0.99    m1_pre_topc(sK3,sK1)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f68,plain,(
% 1.48/0.99    l1_pre_topc(sK1)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f72,plain,(
% 1.48/0.99    ~v2_struct_0(sK3)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f70,plain,(
% 1.48/0.99    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f11,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f29,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f11])).
% 1.48/0.99  
% 1.48/0.99  fof(f30,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f29])).
% 1.48/0.99  
% 1.48/0.99  fof(f37,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f62,plain,(
% 1.48/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f37])).
% 1.48/0.99  
% 1.48/0.99  fof(f86,plain,(
% 1.48/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(equality_resolution,[],[f62])).
% 1.48/0.99  
% 1.48/0.99  fof(f2,axiom,(
% 1.48/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f14,plain,(
% 1.48/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.48/0.99    inference(ennf_transformation,[],[f2])).
% 1.48/0.99  
% 1.48/0.99  fof(f15,plain,(
% 1.48/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.48/0.99    inference(flattening,[],[f14])).
% 1.48/0.99  
% 1.48/0.99  fof(f50,plain,(
% 1.48/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f15])).
% 1.48/0.99  
% 1.48/0.99  fof(f7,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f22,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f7])).
% 1.48/0.99  
% 1.48/0.99  fof(f23,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f22])).
% 1.48/0.99  
% 1.48/0.99  fof(f55,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f23])).
% 1.48/0.99  
% 1.48/0.99  fof(f8,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f24,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f8])).
% 1.48/0.99  
% 1.48/0.99  fof(f25,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.99    inference(flattening,[],[f24])).
% 1.48/0.99  
% 1.48/0.99  fof(f35,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f25])).
% 1.48/0.99  
% 1.48/0.99  fof(f36,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.99    inference(flattening,[],[f35])).
% 1.48/0.99  
% 1.48/0.99  fof(f56,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f36])).
% 1.48/0.99  
% 1.48/0.99  fof(f84,plain,(
% 1.48/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.99    inference(equality_resolution,[],[f56])).
% 1.48/0.99  
% 1.48/0.99  fof(f9,axiom,(
% 1.48/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f26,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.99    inference(ennf_transformation,[],[f9])).
% 1.48/0.99  
% 1.48/0.99  fof(f59,plain,(
% 1.48/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f73,plain,(
% 1.48/0.99    v1_tsep_1(sK3,sK1)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f67,plain,(
% 1.48/0.99    v2_pre_topc(sK1)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f66,plain,(
% 1.48/0.99    ~v2_struct_0(sK1)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f69,plain,(
% 1.48/0.99    v1_funct_1(sK2)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f6,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f20,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f6])).
% 1.48/0.99  
% 1.48/0.99  fof(f21,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f54,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f21])).
% 1.48/0.99  
% 1.48/0.99  fof(f1,axiom,(
% 1.48/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f33,plain,(
% 1.48/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.99    inference(nnf_transformation,[],[f1])).
% 1.48/0.99  
% 1.48/0.99  fof(f34,plain,(
% 1.48/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.99    inference(flattening,[],[f33])).
% 1.48/0.99  
% 1.48/0.99  fof(f48,plain,(
% 1.48/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.99    inference(cnf_transformation,[],[f34])).
% 1.48/0.99  
% 1.48/0.99  fof(f80,plain,(
% 1.48/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.99    inference(equality_resolution,[],[f48])).
% 1.48/0.99  
% 1.48/0.99  fof(f64,plain,(
% 1.48/0.99    v2_pre_topc(sK0)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f63,plain,(
% 1.48/0.99    ~v2_struct_0(sK0)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f65,plain,(
% 1.48/0.99    l1_pre_topc(sK0)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f71,plain,(
% 1.48/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f61,plain,(
% 1.48/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f37])).
% 1.48/0.99  
% 1.48/0.99  fof(f87,plain,(
% 1.48/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(equality_resolution,[],[f61])).
% 1.48/0.99  
% 1.48/0.99  fof(f10,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f27,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f10])).
% 1.48/0.99  
% 1.48/0.99  fof(f28,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f27])).
% 1.48/0.99  
% 1.48/0.99  fof(f60,plain,(
% 1.48/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f28])).
% 1.48/0.99  
% 1.48/0.99  fof(f85,plain,(
% 1.48/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(equality_resolution,[],[f60])).
% 1.48/0.99  
% 1.48/0.99  fof(f79,plain,(
% 1.48/0.99    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f77,plain,(
% 1.48/0.99    sK4 = sK5),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f78,plain,(
% 1.48/0.99    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  fof(f76,plain,(
% 1.48/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.48/0.99    inference(cnf_transformation,[],[f46])).
% 1.48/0.99  
% 1.48/0.99  cnf(c_4,plain,
% 1.48/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_6,plain,
% 1.48/0.99      ( v2_struct_0(X0)
% 1.48/0.99      | ~ l1_struct_0(X0)
% 1.48/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_411,plain,
% 1.48/0.99      ( v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_5,plain,
% 1.48/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_21,negated_conjecture,
% 1.48/0.99      ( m1_pre_topc(sK3,sK1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_964,plain,
% 1.48/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_965,plain,
% 1.48/0.99      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_964]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_27,negated_conjecture,
% 1.48/0.99      ( l1_pre_topc(sK1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_967,plain,
% 1.48/0.99      ( l1_pre_topc(sK3) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_965,c_27]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1279,plain,
% 1.48/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_411,c_967]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1280,plain,
% 1.48/0.99      ( v2_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_1279]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_23,negated_conjecture,
% 1.48/0.99      ( ~ v2_struct_0(sK3) ),
% 1.48/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1282,plain,
% 1.48/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1280,c_23]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_25,negated_conjecture,
% 1.48/0.99      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_14,plain,
% 1.48/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.48/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.48/0.99      | ~ m1_pre_topc(X4,X0)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X4)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_8,plain,
% 1.48/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.48/0.99      | ~ v3_pre_topc(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,X0)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_11,plain,
% 1.48/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.48/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.48/0.99      | ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_12,plain,
% 1.48/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_178,plain,
% 1.48/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.48/0.99      | ~ v1_tsep_1(X0,X1)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_11,c_12]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_179,plain,
% 1.48/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.48/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.48/0.99      | ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_22,negated_conjecture,
% 1.48/0.99      ( v1_tsep_1(sK3,sK1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_494,plain,
% 1.48/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.48/0.99      | ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | sK1 != X1
% 1.48/0.99      | sK3 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_179,c_22]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_495,plain,
% 1.48/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.48/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.48/0.99      | ~ v2_pre_topc(sK1)
% 1.48/0.99      | ~ l1_pre_topc(sK1) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_28,negated_conjecture,
% 1.48/0.99      ( v2_pre_topc(sK1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_497,plain,
% 1.48/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_495,c_28,c_27,c_21]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_507,plain,
% 1.48/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,X0)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | u1_struct_0(sK3) != X0
% 1.48/0.99      | sK1 != X1 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_497]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_508,plain,
% 1.48/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.48/0.99      | ~ v2_pre_topc(sK1)
% 1.48/0.99      | v2_struct_0(sK1)
% 1.48/0.99      | ~ l1_pre_topc(sK1) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_29,negated_conjecture,
% 1.48/0.99      ( ~ v2_struct_0(sK1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_512,plain,
% 1.48/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_508,c_29,c_28,c_27]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_513,plain,
% 1.48/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_512]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_536,plain,
% 1.48/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.48/0.99      | ~ m1_subset_1(X1,X2)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | v1_xboole_0(X2)
% 1.48/0.99      | X0 != X1
% 1.48/0.99      | u1_struct_0(sK3) != X2 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_513]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_537,plain,
% 1.48/0.99      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_596,plain,
% 1.48/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.48/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/0.99      | ~ m1_pre_topc(X4,X0)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X6,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X6,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X4)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | X6 != X3
% 1.48/0.99      | u1_struct_0(sK3) != X5
% 1.48/0.99      | sK1 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_537]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_597,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.48/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.48/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ v2_pre_topc(sK1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(sK1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(sK1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_596]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_601,plain,
% 1.48/0.99      ( ~ l1_pre_topc(X1)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.48/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.48/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_597,c_29,c_28,c_27]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_602,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.48/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.48/0.99      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_601]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_820,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.48/0.99      | r1_tmap_1(sK1,X1,X2,X3)
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v1_funct_1(X2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.48/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.48/0.99      | sK2 != X2 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_602]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_821,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.48/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v1_funct_1(sK2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_820]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_26,negated_conjecture,
% 1.48/0.99      ( v1_funct_1(sK2) ),
% 1.48/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_825,plain,
% 1.48/0.99      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.48/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_821,c_26]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_826,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.48/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.48/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_825]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1014,plain,
% 1.48/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.48/0.99      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.48/0.99      | sK1 != sK1
% 1.48/0.99      | sK3 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_826]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1015,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(sK3)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_1014]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_935,plain,
% 1.48/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | sK1 != X1
% 1.48/0.99      | sK3 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_936,plain,
% 1.48/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.48/0.99      | ~ l1_pre_topc(sK1) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_935]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1019,plain,
% 1.48/0.99      ( v2_struct_0(X0)
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1015,c_27,c_23,c_936]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1020,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_1019]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_7,plain,
% 1.48/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_946,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.48/0.99      | m1_subset_1(X0,u1_struct_0(X2))
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(X2)
% 1.48/0.99      | ~ l1_pre_topc(X2)
% 1.48/0.99      | sK1 != X2
% 1.48/0.99      | sK3 != X1 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_947,plain,
% 1.48/0.99      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | v2_struct_0(sK1)
% 1.48/0.99      | v2_struct_0(sK3)
% 1.48/0.99      | ~ l1_pre_topc(sK1) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_946]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_951,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_947,c_29,c_27,c_23]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_952,plain,
% 1.48/0.99      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_951]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1036,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(forward_subsumption_resolution,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1020,c_952]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1,plain,
% 1.48/0.99      ( r1_tarski(X0,X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1047,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(forward_subsumption_resolution,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1036,c_1]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_31,negated_conjecture,
% 1.48/0.99      ( v2_pre_topc(sK0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1182,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/0.99      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.48/0.99      | sK0 != X0 ),
% 1.48/0.99      inference(resolution_lifted,[status(thm)],[c_1047,c_31]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1183,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.48/0.99      | v2_struct_0(sK0)
% 1.48/0.99      | ~ l1_pre_topc(sK0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(unflattening,[status(thm)],[c_1182]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_32,negated_conjecture,
% 1.48/0.99      ( ~ v2_struct_0(sK0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_30,negated_conjecture,
% 1.48/0.99      ( l1_pre_topc(sK0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_24,negated_conjecture,
% 1.48/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1187,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/0.99      | r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1183,c_32,c_30,c_24]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1188,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.48/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_1187]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1296,plain,
% 1.48/0.99      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/0.99      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(backward_subsumption_resolution,
% 1.48/1.00                [status(thm)],
% 1.48/1.00                [c_1282,c_1188]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1317,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.48/1.00      inference(equality_resolution_simp,[status(thm)],[c_1296]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1940,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.48/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.48/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.48/1.00      inference(instantiation,[status(thm)],[c_1317]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_15,plain,
% 1.48/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.48/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.48/1.00      | ~ m1_pre_topc(X4,X0)
% 1.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.48/1.00      | ~ v1_funct_1(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X4)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | ~ l1_pre_topc(X0) ),
% 1.48/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_13,plain,
% 1.48/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.48/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/1.00      | ~ m1_pre_topc(X4,X0)
% 1.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ v1_funct_1(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X4)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | ~ l1_pre_topc(X0) ),
% 1.48/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_170,plain,
% 1.48/1.00      ( ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.48/1.00      | ~ m1_pre_topc(X4,X0)
% 1.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/1.00      | ~ v1_funct_1(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X4)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | ~ l1_pre_topc(X0) ),
% 1.48/1.00      inference(global_propositional_subsumption,
% 1.48/1.00                [status(thm)],
% 1.48/1.00                [c_15,c_13]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_171,plain,
% 1.48/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.48/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.48/1.00      | ~ m1_pre_topc(X4,X0)
% 1.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ v1_funct_1(X2)
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X4)
% 1.48/1.00      | ~ l1_pre_topc(X0)
% 1.48/1.00      | ~ l1_pre_topc(X1) ),
% 1.48/1.00      inference(renaming,[status(thm)],[c_170]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_714,plain,
% 1.48/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.48/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.48/1.00      | ~ m1_pre_topc(X4,X0)
% 1.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ v1_funct_1(X2)
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X4)
% 1.48/1.00      | ~ l1_pre_topc(X0)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.48/1.00      | sK2 != X2 ),
% 1.48/1.00      inference(resolution_lifted,[status(thm)],[c_171,c_25]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_715,plain,
% 1.48/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.48/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.48/1.00      | ~ m1_pre_topc(X0,X2)
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.48/1.00      | ~ v1_funct_1(sK2)
% 1.48/1.00      | ~ v2_pre_topc(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | v2_struct_0(X2)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | ~ l1_pre_topc(X2)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(unflattening,[status(thm)],[c_714]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_719,plain,
% 1.48/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_pre_topc(X0,X2)
% 1.48/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.48/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.48/1.00      | ~ v2_pre_topc(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | v2_struct_0(X2)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | ~ l1_pre_topc(X2)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(global_propositional_subsumption,
% 1.48/1.00                [status(thm)],
% 1.48/1.00                [c_715,c_26]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_720,plain,
% 1.48/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.48/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.48/1.00      | ~ m1_pre_topc(X0,X2)
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | ~ v2_pre_topc(X2)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X2)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | ~ l1_pre_topc(X2)
% 1.48/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(renaming,[status(thm)],[c_719]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_755,plain,
% 1.48/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.48/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.48/1.00      | ~ m1_pre_topc(X0,X2)
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | ~ v2_pre_topc(X2)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | v2_struct_0(X2)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | ~ l1_pre_topc(X2)
% 1.48/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_720,c_7]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_975,plain,
% 1.48/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.48/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.48/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.48/1.00      | ~ v2_pre_topc(X2)
% 1.48/1.00      | ~ v2_pre_topc(X1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(X2)
% 1.48/1.00      | v2_struct_0(X1)
% 1.48/1.00      | ~ l1_pre_topc(X2)
% 1.48/1.00      | ~ l1_pre_topc(X1)
% 1.48/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.48/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.48/1.00      | sK1 != X2
% 1.48/1.00      | sK3 != X0 ),
% 1.48/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_755]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_976,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | ~ v2_pre_topc(sK1)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | v2_struct_0(sK1)
% 1.48/1.00      | v2_struct_0(sK3)
% 1.48/1.00      | ~ l1_pre_topc(X0)
% 1.48/1.00      | ~ l1_pre_topc(sK1)
% 1.48/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.48/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.48/1.00      inference(unflattening,[status(thm)],[c_975]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_980,plain,
% 1.48/1.00      ( ~ l1_pre_topc(X0)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.48/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.48/1.00      inference(global_propositional_subsumption,
% 1.48/1.00                [status(thm)],
% 1.48/1.00                [c_976,c_29,c_28,c_27,c_23]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_981,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/1.00      | ~ v2_pre_topc(X0)
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | ~ l1_pre_topc(X0)
% 1.48/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.48/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.48/1.00      inference(renaming,[status(thm)],[c_980]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1209,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,X0,sK2,X1)
% 1.48/1.00      | r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
% 1.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 1.48/1.00      | v2_struct_0(X0)
% 1.48/1.00      | ~ l1_pre_topc(X0)
% 1.48/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.48/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.48/1.00      | sK0 != X0 ),
% 1.48/1.00      inference(resolution_lifted,[status(thm)],[c_981,c_31]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1210,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.48/1.00      | v2_struct_0(sK0)
% 1.48/1.00      | ~ l1_pre_topc(sK0)
% 1.48/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(unflattening,[status(thm)],[c_1209]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1214,plain,
% 1.48/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(global_propositional_subsumption,
% 1.48/1.00                [status(thm)],
% 1.48/1.00                [c_1210,c_32,c_30,c_24]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1215,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.48/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.48/1.00      inference(renaming,[status(thm)],[c_1214]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1322,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
% 1.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.48/1.00      inference(equality_resolution_simp,[status(thm)],[c_1215]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1937,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
% 1.48/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.48/1.00      inference(instantiation,[status(thm)],[c_1322]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_16,negated_conjecture,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.48/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.48/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1823,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.48/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_18,negated_conjecture,
% 1.48/1.00      ( sK4 = sK5 ),
% 1.48/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1854,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.48/1.00      inference(light_normalisation,[status(thm)],[c_1823,c_18]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1905,plain,
% 1.48/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.48/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.48/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1854]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_17,negated_conjecture,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.48/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1822,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.48/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1849,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.48/1.00      inference(light_normalisation,[status(thm)],[c_1822,c_18]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_1899,plain,
% 1.48/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5)
% 1.48/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.48/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1849]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(c_19,negated_conjecture,
% 1.48/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.48/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.48/1.00  
% 1.48/1.00  cnf(contradiction,plain,
% 1.48/1.00      ( $false ),
% 1.48/1.00      inference(minisat,[status(thm)],[c_1940,c_1937,c_1905,c_1899,c_19]) ).
% 1.48/1.00  
% 1.48/1.00  
% 1.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.48/1.00  
% 1.48/1.00  ------                               Statistics
% 1.48/1.00  
% 1.48/1.00  ------ General
% 1.48/1.00  
% 1.48/1.00  abstr_ref_over_cycles:                  0
% 1.48/1.00  abstr_ref_under_cycles:                 0
% 1.48/1.00  gc_basic_clause_elim:                   0
% 1.48/1.00  forced_gc_time:                         0
% 1.48/1.00  parsing_time:                           0.01
% 1.48/1.00  unif_index_cands_time:                  0.
% 1.48/1.00  unif_index_add_time:                    0.
% 1.48/1.00  orderings_time:                         0.
% 1.48/1.00  out_proof_time:                         0.013
% 1.48/1.00  total_time:                             0.097
% 1.48/1.00  num_of_symbols:                         58
% 1.48/1.00  num_of_terms:                           1105
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing
% 1.48/1.00  
% 1.48/1.00  num_of_splits:                          2
% 1.48/1.00  num_of_split_atoms:                     2
% 1.48/1.00  num_of_reused_defs:                     0
% 1.48/1.00  num_eq_ax_congr_red:                    12
% 1.48/1.00  num_of_sem_filtered_clauses:            1
% 1.48/1.00  num_of_subtypes:                        0
% 1.48/1.00  monotx_restored_types:                  0
% 1.48/1.00  sat_num_of_epr_types:                   0
% 1.48/1.00  sat_num_of_non_cyclic_types:            0
% 1.48/1.00  sat_guarded_non_collapsed_types:        0
% 1.48/1.00  num_pure_diseq_elim:                    0
% 1.48/1.00  simp_replaced_by:                       0
% 1.48/1.00  res_preprocessed:                       94
% 1.48/1.00  prep_upred:                             0
% 1.48/1.00  prep_unflattend:                        31
% 1.48/1.00  smt_new_axioms:                         0
% 1.48/1.00  pred_elim_cands:                        3
% 1.48/1.00  pred_elim:                              12
% 1.48/1.00  pred_elim_cl:                           17
% 1.48/1.00  pred_elim_cycles:                       20
% 1.48/1.00  merged_defs:                            8
% 1.48/1.00  merged_defs_ncl:                        0
% 1.48/1.00  bin_hyper_res:                          8
% 1.48/1.00  prep_cycles:                            4
% 1.48/1.00  pred_elim_time:                         0.028
% 1.48/1.00  splitting_time:                         0.
% 1.48/1.00  sem_filter_time:                        0.
% 1.48/1.00  monotx_time:                            0.
% 1.48/1.00  subtype_inf_time:                       0.
% 1.48/1.00  
% 1.48/1.00  ------ Problem properties
% 1.48/1.00  
% 1.48/1.00  clauses:                                16
% 1.48/1.00  conjectures:                            6
% 1.48/1.00  epr:                                    3
% 1.48/1.00  horn:                                   15
% 1.48/1.00  ground:                                 9
% 1.48/1.00  unary:                                  6
% 1.48/1.00  binary:                                 3
% 1.48/1.00  lits:                                   35
% 1.48/1.00  lits_eq:                                4
% 1.48/1.00  fd_pure:                                0
% 1.48/1.00  fd_pseudo:                              0
% 1.48/1.00  fd_cond:                                0
% 1.48/1.00  fd_pseudo_cond:                         1
% 1.48/1.00  ac_symbols:                             0
% 1.48/1.00  
% 1.48/1.00  ------ Propositional Solver
% 1.48/1.00  
% 1.48/1.00  prop_solver_calls:                      23
% 1.48/1.00  prop_fast_solver_calls:                 896
% 1.48/1.00  smt_solver_calls:                       0
% 1.48/1.00  smt_fast_solver_calls:                  0
% 1.48/1.00  prop_num_of_clauses:                    326
% 1.48/1.00  prop_preprocess_simplified:             2205
% 1.48/1.00  prop_fo_subsumed:                       42
% 1.48/1.00  prop_solver_time:                       0.
% 1.48/1.00  smt_solver_time:                        0.
% 1.48/1.00  smt_fast_solver_time:                   0.
% 1.48/1.00  prop_fast_solver_time:                  0.
% 1.48/1.00  prop_unsat_core_time:                   0.
% 1.48/1.00  
% 1.48/1.00  ------ QBF
% 1.48/1.00  
% 1.48/1.00  qbf_q_res:                              0
% 1.48/1.00  qbf_num_tautologies:                    0
% 1.48/1.00  qbf_prep_cycles:                        0
% 1.48/1.00  
% 1.48/1.00  ------ BMC1
% 1.48/1.00  
% 1.48/1.00  bmc1_current_bound:                     -1
% 1.48/1.00  bmc1_last_solved_bound:                 -1
% 1.48/1.00  bmc1_unsat_core_size:                   -1
% 1.48/1.00  bmc1_unsat_core_parents_size:           -1
% 1.48/1.00  bmc1_merge_next_fun:                    0
% 1.48/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.48/1.00  
% 1.48/1.00  ------ Instantiation
% 1.48/1.00  
% 1.48/1.00  inst_num_of_clauses:                    36
% 1.48/1.00  inst_num_in_passive:                    9
% 1.48/1.00  inst_num_in_active:                     25
% 1.48/1.00  inst_num_in_unprocessed:                1
% 1.48/1.00  inst_num_of_loops:                      27
% 1.48/1.00  inst_num_of_learning_restarts:          0
% 1.48/1.00  inst_num_moves_active_passive:          0
% 1.48/1.00  inst_lit_activity:                      0
% 1.48/1.00  inst_lit_activity_moves:                0
% 1.48/1.00  inst_num_tautologies:                   0
% 1.48/1.00  inst_num_prop_implied:                  0
% 1.48/1.00  inst_num_existing_simplified:           0
% 1.48/1.00  inst_num_eq_res_simplified:             0
% 1.48/1.00  inst_num_child_elim:                    0
% 1.48/1.00  inst_num_of_dismatching_blockings:      0
% 1.48/1.00  inst_num_of_non_proper_insts:           12
% 1.48/1.00  inst_num_of_duplicates:                 0
% 1.48/1.00  inst_inst_num_from_inst_to_res:         0
% 1.48/1.00  inst_dismatching_checking_time:         0.
% 1.48/1.00  
% 1.48/1.00  ------ Resolution
% 1.48/1.00  
% 1.48/1.00  res_num_of_clauses:                     0
% 1.48/1.00  res_num_in_passive:                     0
% 1.48/1.00  res_num_in_active:                      0
% 1.48/1.00  res_num_of_loops:                       98
% 1.48/1.00  res_forward_subset_subsumed:            0
% 1.48/1.00  res_backward_subset_subsumed:           0
% 1.48/1.00  res_forward_subsumed:                   0
% 1.48/1.00  res_backward_subsumed:                  0
% 1.48/1.00  res_forward_subsumption_resolution:     3
% 1.48/1.00  res_backward_subsumption_resolution:    2
% 1.48/1.00  res_clause_to_clause_subsumption:       94
% 1.48/1.00  res_orphan_elimination:                 0
% 1.48/1.00  res_tautology_del:                      18
% 1.48/1.00  res_num_eq_res_simplified:              2
% 1.48/1.00  res_num_sel_changes:                    0
% 1.48/1.00  res_moves_from_active_to_pass:          0
% 1.48/1.00  
% 1.48/1.00  ------ Superposition
% 1.48/1.00  
% 1.48/1.00  sup_time_total:                         0.
% 1.48/1.00  sup_time_generating:                    0.
% 1.48/1.00  sup_time_sim_full:                      0.
% 1.48/1.00  sup_time_sim_immed:                     0.
% 1.48/1.00  
% 1.48/1.00  sup_num_of_clauses:                     16
% 1.48/1.00  sup_num_in_active:                      4
% 1.48/1.00  sup_num_in_passive:                     12
% 1.48/1.00  sup_num_of_loops:                       4
% 1.48/1.00  sup_fw_superposition:                   0
% 1.48/1.00  sup_bw_superposition:                   0
% 1.48/1.00  sup_immediate_simplified:               0
% 1.48/1.00  sup_given_eliminated:                   0
% 1.48/1.00  comparisons_done:                       0
% 1.48/1.00  comparisons_avoided:                    0
% 1.48/1.00  
% 1.48/1.00  ------ Simplifications
% 1.48/1.00  
% 1.48/1.00  
% 1.48/1.00  sim_fw_subset_subsumed:                 0
% 1.48/1.00  sim_bw_subset_subsumed:                 0
% 1.48/1.00  sim_fw_subsumed:                        0
% 1.48/1.00  sim_bw_subsumed:                        0
% 1.48/1.00  sim_fw_subsumption_res:                 0
% 1.48/1.00  sim_bw_subsumption_res:                 0
% 1.48/1.00  sim_tautology_del:                      0
% 1.48/1.00  sim_eq_tautology_del:                   0
% 1.48/1.00  sim_eq_res_simp:                        0
% 1.48/1.00  sim_fw_demodulated:                     0
% 1.48/1.00  sim_bw_demodulated:                     0
% 1.48/1.00  sim_light_normalised:                   3
% 1.48/1.00  sim_joinable_taut:                      0
% 1.48/1.00  sim_joinable_simp:                      0
% 1.48/1.00  sim_ac_normalised:                      0
% 1.48/1.00  sim_smt_subsumption:                    0
% 1.48/1.00  
%------------------------------------------------------------------------------
