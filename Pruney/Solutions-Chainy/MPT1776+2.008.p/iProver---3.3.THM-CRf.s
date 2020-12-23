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
% DateTime   : Thu Dec  3 12:23:22 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 488 expanded)
%              Number of clauses        :   90 (  98 expanded)
%              Number of leaves         :   14 ( 201 expanded)
%              Depth                    :   21
%              Number of atoms          : 1232 (9515 expanded)
%              Number of equality atoms :  187 ( 681 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   46 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X5)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X0,X4,X5) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | r1_tmap_1(X3,X0,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X0,X4,sK5) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK5) )
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X0,X4,X5) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X2,X1)
          & v1_tsep_1(X2,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | ~ r1_tmap_1(X3,X0,sK4,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | r1_tmap_1(X3,X0,sK4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X0,X4,X5) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X2,X1)
              & v1_tsep_1(X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | ~ r1_tmap_1(sK3,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | r1_tmap_1(sK3,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X0,X4,X5) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,X1)
                  & v1_tsep_1(X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(sK2,X1)
                & v1_tsep_1(sK2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK1)
                    & v1_tsep_1(X2,sK1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK0,X4,X5) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK2,sK1)
    & v1_tsep_1(sK2,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f41,f40,f39,f38,f37,f36,f35])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_571,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_572,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_576,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_22])).

cnf(c_577,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_620,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_577,c_9])).

cnf(c_1118,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,X3_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_2304,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK3,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_2669,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,X1_51)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_3069,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2669])).

cnf(c_3284,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,sK6)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_3295,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3284])).

cnf(c_3297,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3295])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_640,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_641,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_645,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_22])).

cnf(c_646,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_689,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_646,c_9])).

cnf(c_1117,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
    | r1_tmap_1(X3_51,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,X3_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_2305,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
    | r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK3,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_2668,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,X1_51)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2305])).

cnf(c_3037,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2668])).

cnf(c_3285,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_3291,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3285])).

cnf(c_3293,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_7,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1140,plain,
    ( r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2597,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_2598,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1144,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2352,plain,
    ( ~ m1_pre_topc(sK3,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_2523,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_2524,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2523])).

cnf(c_1148,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2358,plain,
    ( u1_struct_0(X0_51) = u1_struct_0(X0_51) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_2363,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_5,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1142,plain,
    ( ~ v1_tsep_1(X0_51,X1_51)
    | v1_tsep_1(X0_51,X2_51)
    | ~ r1_tarski(u1_struct_0(X0_51),u1_struct_0(X2_51))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2241,plain,
    ( v1_tsep_1(sK2,X0_51)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_51))
    | ~ m1_pre_topc(X0_51,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2291,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_2292,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | v1_tsep_1(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2291])).

cnf(c_2196,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1138,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1845,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_14,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1136,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1921,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1845,c_1136])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1134,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1848,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_1895,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1848,c_1136])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1137,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1846,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_1916,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1846,c_1136])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_48,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_46,plain,
    ( v1_tsep_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3297,c_3293,c_2598,c_2524,c_2363,c_2292,c_2196,c_1921,c_1895,c_1916,c_50,c_48,c_46,c_45,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.13/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/1.00  
% 2.13/1.00  ------  iProver source info
% 2.13/1.00  
% 2.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/1.00  git: non_committed_changes: false
% 2.13/1.00  git: last_make_outside_of_git: false
% 2.13/1.00  
% 2.13/1.00  ------ 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options
% 2.13/1.00  
% 2.13/1.00  --out_options                           all
% 2.13/1.00  --tptp_safe_out                         true
% 2.13/1.00  --problem_path                          ""
% 2.13/1.00  --include_path                          ""
% 2.13/1.00  --clausifier                            res/vclausify_rel
% 2.13/1.00  --clausifier_options                    --mode clausify
% 2.13/1.00  --stdin                                 false
% 2.13/1.00  --stats_out                             all
% 2.13/1.00  
% 2.13/1.00  ------ General Options
% 2.13/1.00  
% 2.13/1.00  --fof                                   false
% 2.13/1.00  --time_out_real                         305.
% 2.13/1.00  --time_out_virtual                      -1.
% 2.13/1.00  --symbol_type_check                     false
% 2.13/1.00  --clausify_out                          false
% 2.13/1.00  --sig_cnt_out                           false
% 2.13/1.00  --trig_cnt_out                          false
% 2.13/1.00  --trig_cnt_out_tolerance                1.
% 2.13/1.00  --trig_cnt_out_sk_spl                   false
% 2.13/1.00  --abstr_cl_out                          false
% 2.13/1.00  
% 2.13/1.00  ------ Global Options
% 2.13/1.00  
% 2.13/1.00  --schedule                              default
% 2.13/1.00  --add_important_lit                     false
% 2.13/1.00  --prop_solver_per_cl                    1000
% 2.13/1.00  --min_unsat_core                        false
% 2.13/1.00  --soft_assumptions                      false
% 2.13/1.00  --soft_lemma_size                       3
% 2.13/1.00  --prop_impl_unit_size                   0
% 2.13/1.00  --prop_impl_unit                        []
% 2.13/1.00  --share_sel_clauses                     true
% 2.13/1.00  --reset_solvers                         false
% 2.13/1.00  --bc_imp_inh                            [conj_cone]
% 2.13/1.00  --conj_cone_tolerance                   3.
% 2.13/1.00  --extra_neg_conj                        none
% 2.13/1.00  --large_theory_mode                     true
% 2.13/1.00  --prolific_symb_bound                   200
% 2.13/1.00  --lt_threshold                          2000
% 2.13/1.00  --clause_weak_htbl                      true
% 2.13/1.00  --gc_record_bc_elim                     false
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing Options
% 2.13/1.00  
% 2.13/1.00  --preprocessing_flag                    true
% 2.13/1.00  --time_out_prep_mult                    0.1
% 2.13/1.00  --splitting_mode                        input
% 2.13/1.00  --splitting_grd                         true
% 2.13/1.00  --splitting_cvd                         false
% 2.13/1.00  --splitting_cvd_svl                     false
% 2.13/1.00  --splitting_nvd                         32
% 2.13/1.00  --sub_typing                            true
% 2.13/1.00  --prep_gs_sim                           true
% 2.13/1.00  --prep_unflatten                        true
% 2.13/1.00  --prep_res_sim                          true
% 2.13/1.00  --prep_upred                            true
% 2.13/1.00  --prep_sem_filter                       exhaustive
% 2.13/1.00  --prep_sem_filter_out                   false
% 2.13/1.00  --pred_elim                             true
% 2.13/1.00  --res_sim_input                         true
% 2.13/1.00  --eq_ax_congr_red                       true
% 2.13/1.00  --pure_diseq_elim                       true
% 2.13/1.00  --brand_transform                       false
% 2.13/1.00  --non_eq_to_eq                          false
% 2.13/1.00  --prep_def_merge                        true
% 2.13/1.00  --prep_def_merge_prop_impl              false
% 2.13/1.00  --prep_def_merge_mbd                    true
% 2.13/1.00  --prep_def_merge_tr_red                 false
% 2.13/1.00  --prep_def_merge_tr_cl                  false
% 2.13/1.00  --smt_preprocessing                     true
% 2.13/1.00  --smt_ac_axioms                         fast
% 2.13/1.00  --preprocessed_out                      false
% 2.13/1.00  --preprocessed_stats                    false
% 2.13/1.00  
% 2.13/1.00  ------ Abstraction refinement Options
% 2.13/1.00  
% 2.13/1.00  --abstr_ref                             []
% 2.13/1.00  --abstr_ref_prep                        false
% 2.13/1.00  --abstr_ref_until_sat                   false
% 2.13/1.00  --abstr_ref_sig_restrict                funpre
% 2.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.00  --abstr_ref_under                       []
% 2.13/1.00  
% 2.13/1.00  ------ SAT Options
% 2.13/1.00  
% 2.13/1.00  --sat_mode                              false
% 2.13/1.00  --sat_fm_restart_options                ""
% 2.13/1.00  --sat_gr_def                            false
% 2.13/1.00  --sat_epr_types                         true
% 2.13/1.00  --sat_non_cyclic_types                  false
% 2.13/1.00  --sat_finite_models                     false
% 2.13/1.00  --sat_fm_lemmas                         false
% 2.13/1.00  --sat_fm_prep                           false
% 2.13/1.00  --sat_fm_uc_incr                        true
% 2.13/1.00  --sat_out_model                         small
% 2.13/1.00  --sat_out_clauses                       false
% 2.13/1.00  
% 2.13/1.00  ------ QBF Options
% 2.13/1.00  
% 2.13/1.00  --qbf_mode                              false
% 2.13/1.00  --qbf_elim_univ                         false
% 2.13/1.00  --qbf_dom_inst                          none
% 2.13/1.00  --qbf_dom_pre_inst                      false
% 2.13/1.00  --qbf_sk_in                             false
% 2.13/1.00  --qbf_pred_elim                         true
% 2.13/1.00  --qbf_split                             512
% 2.13/1.00  
% 2.13/1.00  ------ BMC1 Options
% 2.13/1.00  
% 2.13/1.00  --bmc1_incremental                      false
% 2.13/1.00  --bmc1_axioms                           reachable_all
% 2.13/1.00  --bmc1_min_bound                        0
% 2.13/1.00  --bmc1_max_bound                        -1
% 2.13/1.00  --bmc1_max_bound_default                -1
% 2.13/1.00  --bmc1_symbol_reachability              true
% 2.13/1.00  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     num_symb
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       true
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  ------ Parsing...
% 2.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/1.00  ------ Proving...
% 2.13/1.00  ------ Problem Properties 
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  clauses                                 30
% 2.13/1.00  conjectures                             18
% 2.13/1.00  EPR                                     17
% 2.13/1.00  Horn                                    22
% 2.13/1.00  unary                                   16
% 2.13/1.00  binary                                  3
% 2.13/1.00  lits                                    129
% 2.13/1.00  lits eq                                 13
% 2.13/1.00  fd_pure                                 0
% 2.13/1.00  fd_pseudo                               0
% 2.13/1.00  fd_cond                                 0
% 2.13/1.00  fd_pseudo_cond                          0
% 2.13/1.00  AC symbols                              0
% 2.13/1.00  
% 2.13/1.00  ------ Schedule dynamic 5 is on 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ 
% 2.13/1.00  Current options:
% 2.13/1.00  ------ 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options
% 2.13/1.00  
% 2.13/1.00  --out_options                           all
% 2.13/1.00  --tptp_safe_out                         true
% 2.13/1.00  --problem_path                          ""
% 2.13/1.00  --include_path                          ""
% 2.13/1.00  --clausifier                            res/vclausify_rel
% 2.13/1.00  --clausifier_options                    --mode clausify
% 2.13/1.00  --stdin                                 false
% 2.13/1.00  --stats_out                             all
% 2.13/1.00  
% 2.13/1.00  ------ General Options
% 2.13/1.00  
% 2.13/1.00  --fof                                   false
% 2.13/1.00  --time_out_real                         305.
% 2.13/1.00  --time_out_virtual                      -1.
% 2.13/1.00  --symbol_type_check                     false
% 2.13/1.00  --clausify_out                          false
% 2.13/1.00  --sig_cnt_out                           false
% 2.13/1.00  --trig_cnt_out                          false
% 2.13/1.00  --trig_cnt_out_tolerance                1.
% 2.13/1.00  --trig_cnt_out_sk_spl                   false
% 2.13/1.00  --abstr_cl_out                          false
% 2.13/1.00  
% 2.13/1.00  ------ Global Options
% 2.13/1.00  
% 2.13/1.00  --schedule                              default
% 2.13/1.00  --add_important_lit                     false
% 2.13/1.00  --prop_solver_per_cl                    1000
% 2.13/1.00  --min_unsat_core                        false
% 2.13/1.00  --soft_assumptions                      false
% 2.13/1.00  --soft_lemma_size                       3
% 2.13/1.00  --prop_impl_unit_size                   0
% 2.13/1.00  --prop_impl_unit                        []
% 2.13/1.00  --share_sel_clauses                     true
% 2.13/1.00  --reset_solvers                         false
% 2.13/1.00  --bc_imp_inh                            [conj_cone]
% 2.13/1.00  --conj_cone_tolerance                   3.
% 2.13/1.00  --extra_neg_conj                        none
% 2.13/1.00  --large_theory_mode                     true
% 2.13/1.00  --prolific_symb_bound                   200
% 2.13/1.00  --lt_threshold                          2000
% 2.13/1.00  --clause_weak_htbl                      true
% 2.13/1.00  --gc_record_bc_elim                     false
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing Options
% 2.13/1.00  
% 2.13/1.00  --preprocessing_flag                    true
% 2.13/1.00  --time_out_prep_mult                    0.1
% 2.13/1.00  --splitting_mode                        input
% 2.13/1.00  --splitting_grd                         true
% 2.13/1.00  --splitting_cvd                         false
% 2.13/1.00  --splitting_cvd_svl                     false
% 2.13/1.00  --splitting_nvd                         32
% 2.13/1.00  --sub_typing                            true
% 2.13/1.00  --prep_gs_sim                           true
% 2.13/1.00  --prep_unflatten                        true
% 2.13/1.00  --prep_res_sim                          true
% 2.13/1.00  --prep_upred                            true
% 2.13/1.00  --prep_sem_filter                       exhaustive
% 2.13/1.00  --prep_sem_filter_out                   false
% 2.13/1.00  --pred_elim                             true
% 2.13/1.00  --res_sim_input                         true
% 2.13/1.00  --eq_ax_congr_red                       true
% 2.13/1.00  --pure_diseq_elim                       true
% 2.13/1.00  --brand_transform                       false
% 2.13/1.00  --non_eq_to_eq                          false
% 2.13/1.00  --prep_def_merge                        true
% 2.13/1.00  --prep_def_merge_prop_impl              false
% 2.13/1.00  --prep_def_merge_mbd                    true
% 2.13/1.00  --prep_def_merge_tr_red                 false
% 2.13/1.00  --prep_def_merge_tr_cl                  false
% 2.13/1.00  --smt_preprocessing                     true
% 2.13/1.00  --smt_ac_axioms                         fast
% 2.13/1.00  --preprocessed_out                      false
% 2.13/1.00  --preprocessed_stats                    false
% 2.13/1.00  
% 2.13/1.00  ------ Abstraction refinement Options
% 2.13/1.00  
% 2.13/1.00  --abstr_ref                             []
% 2.13/1.00  --abstr_ref_prep                        false
% 2.13/1.00  --abstr_ref_until_sat                   false
% 2.13/1.00  --abstr_ref_sig_restrict                funpre
% 2.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.00  --abstr_ref_under                       []
% 2.13/1.00  
% 2.13/1.00  ------ SAT Options
% 2.13/1.00  
% 2.13/1.00  --sat_mode                              false
% 2.13/1.00  --sat_fm_restart_options                ""
% 2.13/1.00  --sat_gr_def                            false
% 2.13/1.00  --sat_epr_types                         true
% 2.13/1.00  --sat_non_cyclic_types                  false
% 2.13/1.00  --sat_finite_models                     false
% 2.13/1.00  --sat_fm_lemmas                         false
% 2.13/1.00  --sat_fm_prep                           false
% 2.13/1.00  --sat_fm_uc_incr                        true
% 2.13/1.00  --sat_out_model                         small
% 2.13/1.00  --sat_out_clauses                       false
% 2.13/1.00  
% 2.13/1.00  ------ QBF Options
% 2.13/1.00  
% 2.13/1.00  --qbf_mode                              false
% 2.13/1.00  --qbf_elim_univ                         false
% 2.13/1.00  --qbf_dom_inst                          none
% 2.13/1.00  --qbf_dom_pre_inst                      false
% 2.13/1.00  --qbf_sk_in                             false
% 2.13/1.00  --qbf_pred_elim                         true
% 2.13/1.00  --qbf_split                             512
% 2.13/1.00  
% 2.13/1.00  ------ BMC1 Options
% 2.13/1.00  
% 2.13/1.00  --bmc1_incremental                      false
% 2.13/1.00  --bmc1_axioms                           reachable_all
% 2.13/1.00  --bmc1_min_bound                        0
% 2.13/1.00  --bmc1_max_bound                        -1
% 2.13/1.00  --bmc1_max_bound_default                -1
% 2.13/1.00  --bmc1_symbol_reachability              true
% 2.13/1.00  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     none
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       false
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ Proving...
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS status Theorem for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  fof(f10,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f28,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f10])).
% 2.13/1.00  
% 2.13/1.00  fof(f29,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f28])).
% 2.13/1.00  
% 2.13/1.00  fof(f32,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f29])).
% 2.13/1.00  
% 2.13/1.00  fof(f53,plain,(
% 2.13/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f78,plain,(
% 2.13/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f53])).
% 2.13/1.00  
% 2.13/1.00  fof(f11,conjecture,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f12,negated_conjecture,(
% 2.13/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.13/1.00    inference(negated_conjecture,[],[f11])).
% 2.13/1.00  
% 2.13/1.00  fof(f30,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f12])).
% 2.13/1.00  
% 2.13/1.00  fof(f31,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f30])).
% 2.13/1.00  
% 2.13/1.00  fof(f33,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f34,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f33])).
% 2.13/1.00  
% 2.13/1.00  fof(f41,plain,(
% 2.13/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | r1_tmap_1(X3,X0,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f40,plain,(
% 2.13/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f39,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X0,sK4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | r1_tmap_1(X3,X0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f38,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | r1_tmap_1(sK3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f37,plain,(
% 2.13/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,X1) & v1_tsep_1(sK2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f36,plain,(
% 2.13/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f35,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f42,plain,(
% 2.13/1.00    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f41,f40,f39,f38,f37,f36,f35])).
% 2.13/1.00  
% 2.13/1.00  fof(f66,plain,(
% 2.13/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f65,plain,(
% 2.13/1.00    v1_funct_1(sK4)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f9,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f26,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f9])).
% 2.13/1.00  
% 2.13/1.00  fof(f27,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f26])).
% 2.13/1.00  
% 2.13/1.00  fof(f52,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f27])).
% 2.13/1.00  
% 2.13/1.00  fof(f54,plain,(
% 2.13/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f77,plain,(
% 2.13/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f54])).
% 2.13/1.00  
% 2.13/1.00  fof(f7,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f23,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f7])).
% 2.13/1.00  
% 2.13/1.00  fof(f50,plain,(
% 2.13/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f23])).
% 2.13/1.00  
% 2.13/1.00  fof(f2,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f15,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f2])).
% 2.13/1.00  
% 2.13/1.00  fof(f44,plain,(
% 2.13/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f15])).
% 2.13/1.00  
% 2.13/1.00  fof(f5,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f20,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f5])).
% 2.13/1.00  
% 2.13/1.00  fof(f21,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f20])).
% 2.13/1.00  
% 2.13/1.00  fof(f47,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f21])).
% 2.13/1.00  
% 2.13/1.00  fof(f75,plain,(
% 2.13/1.00    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f73,plain,(
% 2.13/1.00    sK5 = sK6),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f71,plain,(
% 2.13/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f74,plain,(
% 2.13/1.00    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f72,plain,(
% 2.13/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f70,plain,(
% 2.13/1.00    m1_pre_topc(sK2,sK3)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f68,plain,(
% 2.13/1.00    v1_tsep_1(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f67,plain,(
% 2.13/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f64,plain,(
% 2.13/1.00    m1_pre_topc(sK3,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f63,plain,(
% 2.13/1.00    ~v2_struct_0(sK3)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f62,plain,(
% 2.13/1.00    m1_pre_topc(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f61,plain,(
% 2.13/1.00    ~v2_struct_0(sK2)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f60,plain,(
% 2.13/1.00    l1_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f59,plain,(
% 2.13/1.00    v2_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f58,plain,(
% 2.13/1.00    ~v2_struct_0(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f57,plain,(
% 2.13/1.00    l1_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f56,plain,(
% 2.13/1.00    v2_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f55,plain,(
% 2.13/1.00    ~v2_struct_0(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  cnf(c_11,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.13/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.13/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.13/1.00      | ~ v1_tsep_1(X4,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_pre_topc(X0,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X0)
% 2.13/1.00      | v2_struct_0(X5)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X4)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | ~ v1_funct_1(X2)
% 2.13/1.00      | ~ l1_pre_topc(X5)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X5)
% 2.13/1.00      | ~ v2_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_21,negated_conjecture,
% 2.13/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_571,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.13/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.13/1.00      | ~ v1_tsep_1(X4,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_pre_topc(X4,X0)
% 2.13/1.00      | ~ m1_pre_topc(X0,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X5)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X4)
% 2.13/1.00      | v2_struct_0(X5)
% 2.13/1.00      | ~ v1_funct_1(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X5)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X5)
% 2.13/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.13/1.00      | sK4 != X2 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_572,plain,
% 2.13/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ v1_funct_1(sK4)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_571]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_22,negated_conjecture,
% 2.13/1.00      ( v1_funct_1(sK4) ),
% 2.13/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_576,plain,
% 2.13/1.00      ( v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_572,c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_577,plain,
% 2.13/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_576]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_9,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ m1_pre_topc(X2,X0)
% 2.13/1.00      | m1_pre_topc(X2,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_620,plain,
% 2.13/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_577,c_9]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1118,plain,
% 2.13/1.00      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
% 2.13/1.00      | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
% 2.13/1.00      | ~ v1_tsep_1(X0_51,X3_51)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 2.13/1.00      | ~ m1_pre_topc(X3_51,X2_51)
% 2.13/1.00      | ~ m1_pre_topc(X0_51,X3_51)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(X2_51)
% 2.13/1.00      | v2_struct_0(X3_51)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X2_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X2_51)
% 2.13/1.00      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_620]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2304,plain,
% 2.13/1.00      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
% 2.13/1.00      | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 2.13/1.00      | ~ v1_tsep_1(X0_51,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 2.13/1.00      | ~ m1_pre_topc(X0_51,sK3)
% 2.13/1.00      | ~ m1_pre_topc(sK3,X2_51)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(X2_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X2_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X2_51)
% 2.13/1.00      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1118]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2669,plain,
% 2.13/1.00      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.13/1.00      | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,X1_51)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2304]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3069,plain,
% 2.13/1.00      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.13/1.00      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2669]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3284,plain,
% 2.13/1.00      ( ~ r1_tmap_1(sK3,X0_51,sK4,sK6)
% 2.13/1.00      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3069]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3295,plain,
% 2.13/1.00      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.13/1.00      | r1_tmap_1(sK3,X0_51,sK4,sK6) != iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) = iProver_top
% 2.13/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.13/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.13/1.00      | v2_struct_0(sK3) = iProver_top
% 2.13/1.00      | v2_struct_0(sK1) = iProver_top
% 2.13/1.00      | v2_struct_0(sK2) = iProver_top
% 2.13/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3284]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3297,plain,
% 2.13/1.00      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.13/1.00      | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
% 2.13/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.13/1.00      | v2_struct_0(sK3) = iProver_top
% 2.13/1.00      | v2_struct_0(sK1) = iProver_top
% 2.13/1.00      | v2_struct_0(sK0) = iProver_top
% 2.13/1.00      | v2_struct_0(sK2) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3295]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_10,plain,
% 2.13/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.13/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.13/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.13/1.00      | ~ v1_tsep_1(X4,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_pre_topc(X0,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X0)
% 2.13/1.00      | v2_struct_0(X5)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X4)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | ~ v1_funct_1(X2)
% 2.13/1.00      | ~ l1_pre_topc(X5)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X5)
% 2.13/1.00      | ~ v2_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_640,plain,
% 2.13/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.13/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.13/1.00      | ~ v1_tsep_1(X4,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.13/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_pre_topc(X4,X0)
% 2.13/1.00      | ~ m1_pre_topc(X0,X5)
% 2.13/1.00      | ~ m1_pre_topc(X4,X5)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X4)
% 2.13/1.00      | v2_struct_0(X5)
% 2.13/1.00      | ~ v1_funct_1(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X5)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X5)
% 2.13/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.13/1.00      | sK4 != X2 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_641,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ v1_funct_1(sK4)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_645,plain,
% 2.13/1.00      ( v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_641,c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_646,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_645]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_689,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.13/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 2.13/1.00      | ~ v1_tsep_1(X0,X3)
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.13/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.13/1.00      | ~ m1_pre_topc(X3,X2)
% 2.13/1.00      | ~ m1_pre_topc(X0,X3)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(X3)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_646,c_9]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1117,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
% 2.13/1.00      | r1_tmap_1(X3_51,X1_51,sK4,X0_52)
% 2.13/1.00      | ~ v1_tsep_1(X0_51,X3_51)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 2.13/1.00      | ~ m1_pre_topc(X3_51,X2_51)
% 2.13/1.00      | ~ m1_pre_topc(X0_51,X3_51)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(X2_51)
% 2.13/1.00      | v2_struct_0(X3_51)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X2_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X2_51)
% 2.13/1.00      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_689]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2305,plain,
% 2.13/1.00      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
% 2.13/1.00      | r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 2.13/1.00      | ~ v1_tsep_1(X0_51,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 2.13/1.00      | ~ m1_pre_topc(X0_51,sK3)
% 2.13/1.00      | ~ m1_pre_topc(sK3,X2_51)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(X2_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X2_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X2_51)
% 2.13/1.00      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2668,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.13/1.00      | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,X1_51)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2305]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3037,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.13/1.00      | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2668]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3285,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,X0_51,sK4,sK6)
% 2.13/1.00      | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.13/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.13/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | v2_struct_0(sK2)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(X0_51)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3037]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3291,plain,
% 2.13/1.00      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.13/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.13/1.00      | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) != iProver_top
% 2.13/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.13/1.00      | v2_struct_0(X0_51) = iProver_top
% 2.13/1.00      | v2_struct_0(sK3) = iProver_top
% 2.13/1.00      | v2_struct_0(sK1) = iProver_top
% 2.13/1.00      | v2_struct_0(sK2) = iProver_top
% 2.13/1.00      | l1_pre_topc(X0_51) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X0_51) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3285]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3293,plain,
% 2.13/1.00      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.13/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.13/1.00      | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
% 2.13/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.13/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.13/1.00      | v2_struct_0(sK3) = iProver_top
% 2.13/1.00      | v2_struct_0(sK1) = iProver_top
% 2.13/1.00      | v2_struct_0(sK0) = iProver_top
% 2.13/1.00      | v2_struct_0(sK2) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3291]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_7,plain,
% 2.13/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.13/1.00      | ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1140,plain,
% 2.13/1.00      ( r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.13/1.00      | ~ m1_pre_topc(X0_51,X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X1_51) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2597,plain,
% 2.13/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK3)
% 2.13/1.00      | ~ l1_pre_topc(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1140]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2598,plain,
% 2.13/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1144,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | l1_pre_topc(X0_51) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2352,plain,
% 2.13/1.00      ( ~ m1_pre_topc(sK3,X0_51)
% 2.13/1.00      | ~ l1_pre_topc(X0_51)
% 2.13/1.00      | l1_pre_topc(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1144]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2523,plain,
% 2.13/1.00      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2352]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2524,plain,
% 2.13/1.00      ( m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK3) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2523]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1148,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2358,plain,
% 2.13/1.00      ( u1_struct_0(X0_51) = u1_struct_0(X0_51) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1148]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2363,plain,
% 2.13/1.00      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2358]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_5,plain,
% 2.13/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.13/1.00      | v1_tsep_1(X0,X2)
% 2.13/1.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.13/1.00      | ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ m1_pre_topc(X2,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1142,plain,
% 2.13/1.00      ( ~ v1_tsep_1(X0_51,X1_51)
% 2.13/1.00      | v1_tsep_1(X0_51,X2_51)
% 2.13/1.00      | ~ r1_tarski(u1_struct_0(X0_51),u1_struct_0(X2_51))
% 2.13/1.00      | ~ m1_pre_topc(X0_51,X1_51)
% 2.13/1.00      | ~ m1_pre_topc(X2_51,X1_51)
% 2.13/1.00      | v2_struct_0(X1_51)
% 2.13/1.00      | v2_struct_0(X2_51)
% 2.13/1.00      | ~ l1_pre_topc(X1_51)
% 2.13/1.00      | ~ v2_pre_topc(X1_51) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2241,plain,
% 2.13/1.00      ( v1_tsep_1(sK2,X0_51)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK1)
% 2.13/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_51))
% 2.13/1.00      | ~ m1_pre_topc(X0_51,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | v2_struct_0(X0_51)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1142]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2291,plain,
% 2.13/1.00      ( v1_tsep_1(sK2,sK3)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK1)
% 2.13/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.13/1.00      | ~ m1_pre_topc(sK3,sK1)
% 2.13/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | v2_struct_0(sK3)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_2241]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2292,plain,
% 2.13/1.00      ( v1_tsep_1(sK2,sK3) = iProver_top
% 2.13/1.00      | v1_tsep_1(sK2,sK1) != iProver_top
% 2.13/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.13/1.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.13/1.00      | v2_struct_0(sK3) = iProver_top
% 2.13/1.00      | v2_struct_0(sK1) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2291]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2196,plain,
% 2.13/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1148]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_12,negated_conjecture,
% 2.13/1.00      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.13/1.00      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.13/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1138,negated_conjecture,
% 2.13/1.00      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.13/1.00      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1845,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_14,negated_conjecture,
% 2.13/1.00      ( sK5 = sK6 ),
% 2.13/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1136,negated_conjecture,
% 2.13/1.00      ( sK5 = sK6 ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1921,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1845,c_1136]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_16,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1134,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1848,plain,
% 2.13/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1895,plain,
% 2.13/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1848,c_1136]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_13,negated_conjecture,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.13/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1137,negated_conjecture,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1846,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1916,plain,
% 2.13/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.13/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1846,c_1136]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_15,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_50,plain,
% 2.13/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_17,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.13/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_48,plain,
% 2.13/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_19,negated_conjecture,
% 2.13/1.00      ( v1_tsep_1(sK2,sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_46,plain,
% 2.13/1.00      ( v1_tsep_1(sK2,sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_20,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_45,plain,
% 2.13/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_23,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK3,sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_42,plain,
% 2.13/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_24,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK3) ),
% 2.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_41,plain,
% 2.13/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_25,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_40,plain,
% 2.13/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_26,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_39,plain,
% 2.13/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_27,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_38,plain,
% 2.13/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_28,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_37,plain,
% 2.13/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_29,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_36,plain,
% 2.13/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_30,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_35,plain,
% 2.13/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_31,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_34,plain,
% 2.13/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_32,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_33,plain,
% 2.13/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(contradiction,plain,
% 2.13/1.00      ( $false ),
% 2.13/1.00      inference(minisat,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_3297,c_3293,c_2598,c_2524,c_2363,c_2292,c_2196,c_1921,
% 2.13/1.00                 c_1895,c_1916,c_50,c_48,c_46,c_45,c_42,c_41,c_40,c_39,
% 2.13/1.00                 c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  ------                               Statistics
% 2.13/1.00  
% 2.13/1.00  ------ General
% 2.13/1.00  
% 2.13/1.00  abstr_ref_over_cycles:                  0
% 2.13/1.00  abstr_ref_under_cycles:                 0
% 2.13/1.00  gc_basic_clause_elim:                   0
% 2.13/1.00  forced_gc_time:                         0
% 2.13/1.00  parsing_time:                           0.012
% 2.13/1.00  unif_index_cands_time:                  0.
% 2.13/1.00  unif_index_add_time:                    0.
% 2.13/1.00  orderings_time:                         0.
% 2.13/1.00  out_proof_time:                         0.011
% 2.13/1.00  total_time:                             0.167
% 2.13/1.00  num_of_symbols:                         55
% 2.13/1.00  num_of_terms:                           2095
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing
% 2.13/1.00  
% 2.13/1.00  num_of_splits:                          0
% 2.13/1.00  num_of_split_atoms:                     0
% 2.13/1.00  num_of_reused_defs:                     0
% 2.13/1.00  num_eq_ax_congr_red:                    25
% 2.13/1.00  num_of_sem_filtered_clauses:            1
% 2.13/1.00  num_of_subtypes:                        4
% 2.13/1.00  monotx_restored_types:                  0
% 2.13/1.01  sat_num_of_epr_types:                   0
% 2.13/1.01  sat_num_of_non_cyclic_types:            0
% 2.13/1.01  sat_guarded_non_collapsed_types:        0
% 2.13/1.01  num_pure_diseq_elim:                    0
% 2.13/1.01  simp_replaced_by:                       0
% 2.13/1.01  res_preprocessed:                       149
% 2.13/1.01  prep_upred:                             0
% 2.13/1.01  prep_unflattend:                        5
% 2.13/1.01  smt_new_axioms:                         0
% 2.13/1.01  pred_elim_cands:                        8
% 2.13/1.01  pred_elim:                              2
% 2.13/1.01  pred_elim_cl:                           2
% 2.13/1.01  pred_elim_cycles:                       5
% 2.13/1.01  merged_defs:                            8
% 2.13/1.01  merged_defs_ncl:                        0
% 2.13/1.01  bin_hyper_res:                          8
% 2.13/1.01  prep_cycles:                            4
% 2.13/1.01  pred_elim_time:                         0.016
% 2.13/1.01  splitting_time:                         0.
% 2.13/1.01  sem_filter_time:                        0.
% 2.13/1.01  monotx_time:                            0.
% 2.13/1.01  subtype_inf_time:                       0.
% 2.13/1.01  
% 2.13/1.01  ------ Problem properties
% 2.13/1.01  
% 2.13/1.01  clauses:                                30
% 2.13/1.01  conjectures:                            18
% 2.13/1.01  epr:                                    17
% 2.13/1.01  horn:                                   22
% 2.13/1.01  ground:                                 18
% 2.13/1.01  unary:                                  16
% 2.13/1.01  binary:                                 3
% 2.13/1.01  lits:                                   129
% 2.13/1.01  lits_eq:                                13
% 2.13/1.01  fd_pure:                                0
% 2.13/1.01  fd_pseudo:                              0
% 2.13/1.01  fd_cond:                                0
% 2.13/1.01  fd_pseudo_cond:                         0
% 2.13/1.01  ac_symbols:                             0
% 2.13/1.01  
% 2.13/1.01  ------ Propositional Solver
% 2.13/1.01  
% 2.13/1.01  prop_solver_calls:                      29
% 2.13/1.01  prop_fast_solver_calls:                 1560
% 2.13/1.01  smt_solver_calls:                       0
% 2.13/1.01  smt_fast_solver_calls:                  0
% 2.13/1.01  prop_num_of_clauses:                    748
% 2.13/1.01  prop_preprocess_simplified:             3873
% 2.13/1.01  prop_fo_subsumed:                       28
% 2.13/1.01  prop_solver_time:                       0.
% 2.13/1.01  smt_solver_time:                        0.
% 2.13/1.01  smt_fast_solver_time:                   0.
% 2.13/1.01  prop_fast_solver_time:                  0.
% 2.13/1.01  prop_unsat_core_time:                   0.
% 2.13/1.01  
% 2.13/1.01  ------ QBF
% 2.13/1.01  
% 2.13/1.01  qbf_q_res:                              0
% 2.13/1.01  qbf_num_tautologies:                    0
% 2.13/1.01  qbf_prep_cycles:                        0
% 2.13/1.01  
% 2.13/1.01  ------ BMC1
% 2.13/1.01  
% 2.13/1.01  bmc1_current_bound:                     -1
% 2.13/1.01  bmc1_last_solved_bound:                 -1
% 2.13/1.01  bmc1_unsat_core_size:                   -1
% 2.13/1.01  bmc1_unsat_core_parents_size:           -1
% 2.13/1.01  bmc1_merge_next_fun:                    0
% 2.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.13/1.01  
% 2.13/1.01  ------ Instantiation
% 2.13/1.01  
% 2.13/1.01  inst_num_of_clauses:                    219
% 2.13/1.01  inst_num_in_passive:                    33
% 2.13/1.01  inst_num_in_active:                     184
% 2.13/1.01  inst_num_in_unprocessed:                1
% 2.13/1.01  inst_num_of_loops:                      210
% 2.13/1.01  inst_num_of_learning_restarts:          0
% 2.13/1.01  inst_num_moves_active_passive:          20
% 2.13/1.01  inst_lit_activity:                      0
% 2.13/1.01  inst_lit_activity_moves:                0
% 2.13/1.01  inst_num_tautologies:                   0
% 2.13/1.01  inst_num_prop_implied:                  0
% 2.13/1.01  inst_num_existing_simplified:           0
% 2.13/1.01  inst_num_eq_res_simplified:             0
% 2.13/1.01  inst_num_child_elim:                    0
% 2.13/1.01  inst_num_of_dismatching_blockings:      26
% 2.13/1.01  inst_num_of_non_proper_insts:           222
% 2.13/1.01  inst_num_of_duplicates:                 0
% 2.13/1.01  inst_inst_num_from_inst_to_res:         0
% 2.13/1.01  inst_dismatching_checking_time:         0.
% 2.13/1.01  
% 2.13/1.01  ------ Resolution
% 2.13/1.01  
% 2.13/1.01  res_num_of_clauses:                     0
% 2.13/1.01  res_num_in_passive:                     0
% 2.13/1.01  res_num_in_active:                      0
% 2.13/1.01  res_num_of_loops:                       153
% 2.13/1.01  res_forward_subset_subsumed:            51
% 2.13/1.01  res_backward_subset_subsumed:           0
% 2.13/1.01  res_forward_subsumed:                   0
% 2.13/1.01  res_backward_subsumed:                  0
% 2.13/1.01  res_forward_subsumption_resolution:     3
% 2.13/1.01  res_backward_subsumption_resolution:    0
% 2.13/1.01  res_clause_to_clause_subsumption:       301
% 2.13/1.01  res_orphan_elimination:                 0
% 2.13/1.01  res_tautology_del:                      68
% 2.13/1.01  res_num_eq_res_simplified:              0
% 2.13/1.01  res_num_sel_changes:                    0
% 2.13/1.01  res_moves_from_active_to_pass:          0
% 2.13/1.01  
% 2.13/1.01  ------ Superposition
% 2.13/1.01  
% 2.13/1.01  sup_time_total:                         0.
% 2.13/1.01  sup_time_generating:                    0.
% 2.13/1.01  sup_time_sim_full:                      0.
% 2.13/1.01  sup_time_sim_immed:                     0.
% 2.13/1.01  
% 2.13/1.01  sup_num_of_clauses:                     49
% 2.13/1.01  sup_num_in_active:                      40
% 2.13/1.01  sup_num_in_passive:                     9
% 2.13/1.01  sup_num_of_loops:                       40
% 2.13/1.01  sup_fw_superposition:                   22
% 2.13/1.01  sup_bw_superposition:                   5
% 2.13/1.01  sup_immediate_simplified:               3
% 2.13/1.01  sup_given_eliminated:                   0
% 2.13/1.01  comparisons_done:                       0
% 2.13/1.01  comparisons_avoided:                    0
% 2.13/1.01  
% 2.13/1.01  ------ Simplifications
% 2.13/1.01  
% 2.13/1.01  
% 2.13/1.01  sim_fw_subset_subsumed:                 3
% 2.13/1.01  sim_bw_subset_subsumed:                 0
% 2.13/1.01  sim_fw_subsumed:                        0
% 2.13/1.01  sim_bw_subsumed:                        0
% 2.13/1.01  sim_fw_subsumption_res:                 2
% 2.13/1.01  sim_bw_subsumption_res:                 0
% 2.13/1.01  sim_tautology_del:                      6
% 2.13/1.01  sim_eq_tautology_del:                   0
% 2.13/1.01  sim_eq_res_simp:                        0
% 2.13/1.01  sim_fw_demodulated:                     0
% 2.13/1.01  sim_bw_demodulated:                     0
% 2.13/1.01  sim_light_normalised:                   3
% 2.13/1.01  sim_joinable_taut:                      0
% 2.13/1.01  sim_joinable_simp:                      0
% 2.13/1.01  sim_ac_normalised:                      0
% 2.13/1.01  sim_smt_subsumption:                    0
% 2.13/1.01  
%------------------------------------------------------------------------------
