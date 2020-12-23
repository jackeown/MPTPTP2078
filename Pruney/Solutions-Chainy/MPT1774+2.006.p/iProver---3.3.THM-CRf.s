%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:12 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 856 expanded)
%              Number of clauses        :  130 ( 168 expanded)
%              Number of leaves         :   24 ( 368 expanded)
%              Depth                    :   22
%              Number of atoms          : 1764 (18024 expanded)
%              Number of equality atoms :  363 (1265 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f68])).

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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f67])).

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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f40])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X0,X4,X6) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | r1_tmap_1(X3,X0,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X0,X4,X6) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | r1_tmap_1(X3,X0,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X1)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X0,X4,sK7) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X0,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X1)
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X0,X4,X6) )
                & X6 = X7
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X0,X4,X6) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X1)
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X0,sK5,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X0,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X0,X4,X6) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X1)
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X0,X4,X6) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X2,X3)
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
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK2)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                  & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK1,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK2)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f41,f49,f48,f47,f46,f45,f44,f43,f42])).

fof(f81,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK0(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK0(X0,X1,X2))
                    & r1_tarski(sK0(X0,X1,X2),X2)
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f85,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f89,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_214,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16])).

cnf(c_215,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_653,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_30])).

cnf(c_654,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_658,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_31])).

cnf(c_659,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_700,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_659,c_15])).

cnf(c_2709,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_3741,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2709])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_50,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1790,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3103,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_3105,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | ~ r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_3106,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3105])).

cnf(c_4122,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3741,c_50,c_3103,c_3106])).

cnf(c_4123,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4122])).

cnf(c_4143,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4123])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7788,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4143,c_42,c_43,c_44,c_54])).

cnf(c_7789,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7788])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2729,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2818,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2729,c_21])).

cnf(c_7804,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7789,c_2818])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_719,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_720,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_724,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_31])).

cnf(c_725,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_724])).

cnf(c_772,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_725,c_15])).

cnf(c_3104,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_connsp_2(X4,sK4,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_3779,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK3,X0,k3_tmap_1(X2,X0,sK4,sK3,sK5),X1)
    | ~ m1_connsp_2(X3,sK4,X1)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X3,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3104])).

cnf(c_3820,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3779])).

cnf(c_4311,plain,
    ( r1_tmap_1(sK4,X0,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7)
    | ~ m1_connsp_2(X1,sK4,sK7)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_6441,plain,
    ( r1_tmap_1(sK4,X0,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7)
    | ~ m1_connsp_2(sK6,sK4,sK7)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4311])).

cnf(c_6442,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7) != iProver_top
    | m1_connsp_2(sK6,sK4,sK7) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6441])).

cnf(c_6444,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top
    | m1_connsp_2(sK6,sK4,sK7) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6442])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4330,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(X1,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5674,plain,
    ( m1_connsp_2(X0,sK4,sK7)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4330])).

cnf(c_6188,plain,
    ( m1_connsp_2(sK6,sK4,sK7)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ r2_hidden(sK7,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5674])).

cnf(c_6189,plain,
    ( m1_connsp_2(sK6,sK4,sK7) = iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6188])).

cnf(c_4448,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_1803,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_3278,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | X2 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | X3 != sK8
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_3590,plain,
    ( r1_tmap_1(X0,X1,X2,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | X2 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | X1 != sK1
    | X0 != sK3
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3278])).

cnf(c_4099,plain,
    ( r1_tmap_1(sK3,X0,X1,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | X1 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | X0 != sK1
    | sK7 != sK8
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3590])).

cnf(c_4447,plain,
    ( r1_tmap_1(sK3,X0,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | X0 != sK1
    | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4099])).

cnf(c_4449,plain,
    ( X0 != sK1
    | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8
    | sK3 != sK3
    | r1_tmap_1(sK3,X0,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4447])).

cnf(c_4451,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8
    | sK1 != sK1
    | sK3 != sK3
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4449])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2719,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2739,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4371,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_2739])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2738,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3887,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_2738])).

cnf(c_3702,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3288,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3620,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3288])).

cnf(c_3621,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3620])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3615,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3618,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3615])).

cnf(c_3473,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_1794,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3169,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_3402,plain,
    ( m1_subset_1(sK7,X0)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3169])).

cnf(c_3472,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_3474,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK7 != sK8
    | m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3472])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3130,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3339,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3130])).

cnf(c_3342,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3339])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3206,plain,
    ( v3_pre_topc(sK6,X0)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3338,plain,
    ( v3_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3206])).

cnf(c_3340,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3338])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2723,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2776,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2723,c_21])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2728,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2807,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2728,c_21])).

cnf(c_1799,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1812,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_107,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_103,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_63,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_61,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_60,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_59,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_58,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_57,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_56,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_55,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_51,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7804,c_6444,c_6189,c_4448,c_4451,c_4371,c_3887,c_3702,c_3621,c_3618,c_3473,c_3474,c_3342,c_3340,c_3103,c_2776,c_2807,c_1812,c_107,c_103,c_63,c_21,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_51,c_50,c_48,c_47,c_46,c_45,c_44,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.05  
% 3.09/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/1.05  
% 3.09/1.05  ------  iProver source info
% 3.09/1.05  
% 3.09/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.09/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/1.05  git: non_committed_changes: false
% 3.09/1.05  git: last_make_outside_of_git: false
% 3.09/1.05  
% 3.09/1.05  ------ 
% 3.09/1.05  
% 3.09/1.05  ------ Input Options
% 3.09/1.05  
% 3.09/1.05  --out_options                           all
% 3.09/1.05  --tptp_safe_out                         true
% 3.09/1.05  --problem_path                          ""
% 3.09/1.05  --include_path                          ""
% 3.09/1.05  --clausifier                            res/vclausify_rel
% 3.09/1.05  --clausifier_options                    --mode clausify
% 3.09/1.05  --stdin                                 false
% 3.09/1.05  --stats_out                             all
% 3.09/1.05  
% 3.09/1.05  ------ General Options
% 3.09/1.05  
% 3.09/1.05  --fof                                   false
% 3.09/1.05  --time_out_real                         305.
% 3.09/1.05  --time_out_virtual                      -1.
% 3.09/1.05  --symbol_type_check                     false
% 3.09/1.05  --clausify_out                          false
% 3.09/1.05  --sig_cnt_out                           false
% 3.09/1.05  --trig_cnt_out                          false
% 3.09/1.05  --trig_cnt_out_tolerance                1.
% 3.09/1.05  --trig_cnt_out_sk_spl                   false
% 3.09/1.05  --abstr_cl_out                          false
% 3.09/1.05  
% 3.09/1.05  ------ Global Options
% 3.09/1.05  
% 3.09/1.05  --schedule                              default
% 3.09/1.05  --add_important_lit                     false
% 3.09/1.05  --prop_solver_per_cl                    1000
% 3.09/1.05  --min_unsat_core                        false
% 3.09/1.05  --soft_assumptions                      false
% 3.09/1.05  --soft_lemma_size                       3
% 3.09/1.05  --prop_impl_unit_size                   0
% 3.09/1.05  --prop_impl_unit                        []
% 3.09/1.05  --share_sel_clauses                     true
% 3.09/1.05  --reset_solvers                         false
% 3.09/1.05  --bc_imp_inh                            [conj_cone]
% 3.09/1.05  --conj_cone_tolerance                   3.
% 3.09/1.05  --extra_neg_conj                        none
% 3.09/1.05  --large_theory_mode                     true
% 3.09/1.05  --prolific_symb_bound                   200
% 3.09/1.05  --lt_threshold                          2000
% 3.09/1.05  --clause_weak_htbl                      true
% 3.09/1.05  --gc_record_bc_elim                     false
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing Options
% 3.09/1.05  
% 3.09/1.05  --preprocessing_flag                    true
% 3.09/1.05  --time_out_prep_mult                    0.1
% 3.09/1.05  --splitting_mode                        input
% 3.09/1.05  --splitting_grd                         true
% 3.09/1.05  --splitting_cvd                         false
% 3.09/1.05  --splitting_cvd_svl                     false
% 3.09/1.05  --splitting_nvd                         32
% 3.09/1.05  --sub_typing                            true
% 3.09/1.05  --prep_gs_sim                           true
% 3.09/1.05  --prep_unflatten                        true
% 3.09/1.05  --prep_res_sim                          true
% 3.09/1.05  --prep_upred                            true
% 3.09/1.05  --prep_sem_filter                       exhaustive
% 3.09/1.05  --prep_sem_filter_out                   false
% 3.09/1.05  --pred_elim                             true
% 3.09/1.05  --res_sim_input                         true
% 3.09/1.05  --eq_ax_congr_red                       true
% 3.09/1.05  --pure_diseq_elim                       true
% 3.09/1.05  --brand_transform                       false
% 3.09/1.05  --non_eq_to_eq                          false
% 3.09/1.05  --prep_def_merge                        true
% 3.09/1.05  --prep_def_merge_prop_impl              false
% 3.09/1.05  --prep_def_merge_mbd                    true
% 3.09/1.05  --prep_def_merge_tr_red                 false
% 3.09/1.05  --prep_def_merge_tr_cl                  false
% 3.09/1.05  --smt_preprocessing                     true
% 3.09/1.05  --smt_ac_axioms                         fast
% 3.09/1.05  --preprocessed_out                      false
% 3.09/1.05  --preprocessed_stats                    false
% 3.09/1.05  
% 3.09/1.05  ------ Abstraction refinement Options
% 3.09/1.05  
% 3.09/1.05  --abstr_ref                             []
% 3.09/1.05  --abstr_ref_prep                        false
% 3.09/1.05  --abstr_ref_until_sat                   false
% 3.09/1.05  --abstr_ref_sig_restrict                funpre
% 3.09/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.05  --abstr_ref_under                       []
% 3.09/1.05  
% 3.09/1.05  ------ SAT Options
% 3.09/1.05  
% 3.09/1.05  --sat_mode                              false
% 3.09/1.05  --sat_fm_restart_options                ""
% 3.09/1.05  --sat_gr_def                            false
% 3.09/1.05  --sat_epr_types                         true
% 3.09/1.05  --sat_non_cyclic_types                  false
% 3.09/1.05  --sat_finite_models                     false
% 3.09/1.05  --sat_fm_lemmas                         false
% 3.09/1.05  --sat_fm_prep                           false
% 3.09/1.05  --sat_fm_uc_incr                        true
% 3.09/1.05  --sat_out_model                         small
% 3.09/1.05  --sat_out_clauses                       false
% 3.09/1.05  
% 3.09/1.05  ------ QBF Options
% 3.09/1.05  
% 3.09/1.05  --qbf_mode                              false
% 3.09/1.05  --qbf_elim_univ                         false
% 3.09/1.05  --qbf_dom_inst                          none
% 3.09/1.05  --qbf_dom_pre_inst                      false
% 3.09/1.05  --qbf_sk_in                             false
% 3.09/1.05  --qbf_pred_elim                         true
% 3.09/1.05  --qbf_split                             512
% 3.09/1.05  
% 3.09/1.05  ------ BMC1 Options
% 3.09/1.05  
% 3.09/1.05  --bmc1_incremental                      false
% 3.09/1.05  --bmc1_axioms                           reachable_all
% 3.09/1.05  --bmc1_min_bound                        0
% 3.09/1.05  --bmc1_max_bound                        -1
% 3.09/1.05  --bmc1_max_bound_default                -1
% 3.09/1.05  --bmc1_symbol_reachability              true
% 3.09/1.05  --bmc1_property_lemmas                  false
% 3.09/1.05  --bmc1_k_induction                      false
% 3.09/1.05  --bmc1_non_equiv_states                 false
% 3.09/1.05  --bmc1_deadlock                         false
% 3.09/1.05  --bmc1_ucm                              false
% 3.09/1.05  --bmc1_add_unsat_core                   none
% 3.09/1.05  --bmc1_unsat_core_children              false
% 3.09/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.05  --bmc1_out_stat                         full
% 3.09/1.05  --bmc1_ground_init                      false
% 3.09/1.05  --bmc1_pre_inst_next_state              false
% 3.09/1.05  --bmc1_pre_inst_state                   false
% 3.09/1.05  --bmc1_pre_inst_reach_state             false
% 3.09/1.05  --bmc1_out_unsat_core                   false
% 3.09/1.05  --bmc1_aig_witness_out                  false
% 3.09/1.05  --bmc1_verbose                          false
% 3.09/1.05  --bmc1_dump_clauses_tptp                false
% 3.09/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.05  --bmc1_dump_file                        -
% 3.09/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.05  --bmc1_ucm_extend_mode                  1
% 3.09/1.05  --bmc1_ucm_init_mode                    2
% 3.09/1.05  --bmc1_ucm_cone_mode                    none
% 3.09/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.05  --bmc1_ucm_relax_model                  4
% 3.09/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.05  --bmc1_ucm_layered_model                none
% 3.09/1.05  --bmc1_ucm_max_lemma_size               10
% 3.09/1.05  
% 3.09/1.05  ------ AIG Options
% 3.09/1.05  
% 3.09/1.05  --aig_mode                              false
% 3.09/1.05  
% 3.09/1.05  ------ Instantiation Options
% 3.09/1.05  
% 3.09/1.05  --instantiation_flag                    true
% 3.09/1.05  --inst_sos_flag                         false
% 3.09/1.05  --inst_sos_phase                        true
% 3.09/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.05  --inst_lit_sel_side                     num_symb
% 3.09/1.05  --inst_solver_per_active                1400
% 3.09/1.05  --inst_solver_calls_frac                1.
% 3.09/1.05  --inst_passive_queue_type               priority_queues
% 3.09/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.05  --inst_passive_queues_freq              [25;2]
% 3.09/1.05  --inst_dismatching                      true
% 3.09/1.05  --inst_eager_unprocessed_to_passive     true
% 3.09/1.05  --inst_prop_sim_given                   true
% 3.09/1.05  --inst_prop_sim_new                     false
% 3.09/1.05  --inst_subs_new                         false
% 3.09/1.05  --inst_eq_res_simp                      false
% 3.09/1.05  --inst_subs_given                       false
% 3.09/1.05  --inst_orphan_elimination               true
% 3.09/1.05  --inst_learning_loop_flag               true
% 3.09/1.05  --inst_learning_start                   3000
% 3.09/1.05  --inst_learning_factor                  2
% 3.09/1.05  --inst_start_prop_sim_after_learn       3
% 3.09/1.05  --inst_sel_renew                        solver
% 3.09/1.05  --inst_lit_activity_flag                true
% 3.09/1.05  --inst_restr_to_given                   false
% 3.09/1.05  --inst_activity_threshold               500
% 3.09/1.05  --inst_out_proof                        true
% 3.09/1.05  
% 3.09/1.05  ------ Resolution Options
% 3.09/1.05  
% 3.09/1.05  --resolution_flag                       true
% 3.09/1.05  --res_lit_sel                           adaptive
% 3.09/1.05  --res_lit_sel_side                      none
% 3.09/1.05  --res_ordering                          kbo
% 3.09/1.05  --res_to_prop_solver                    active
% 3.09/1.05  --res_prop_simpl_new                    false
% 3.09/1.05  --res_prop_simpl_given                  true
% 3.09/1.05  --res_passive_queue_type                priority_queues
% 3.09/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.05  --res_passive_queues_freq               [15;5]
% 3.09/1.05  --res_forward_subs                      full
% 3.09/1.05  --res_backward_subs                     full
% 3.09/1.05  --res_forward_subs_resolution           true
% 3.09/1.05  --res_backward_subs_resolution          true
% 3.09/1.05  --res_orphan_elimination                true
% 3.09/1.05  --res_time_limit                        2.
% 3.09/1.05  --res_out_proof                         true
% 3.09/1.05  
% 3.09/1.05  ------ Superposition Options
% 3.09/1.05  
% 3.09/1.05  --superposition_flag                    true
% 3.09/1.05  --sup_passive_queue_type                priority_queues
% 3.09/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.05  --demod_completeness_check              fast
% 3.09/1.05  --demod_use_ground                      true
% 3.09/1.05  --sup_to_prop_solver                    passive
% 3.09/1.05  --sup_prop_simpl_new                    true
% 3.09/1.05  --sup_prop_simpl_given                  true
% 3.09/1.05  --sup_fun_splitting                     false
% 3.09/1.05  --sup_smt_interval                      50000
% 3.09/1.05  
% 3.09/1.05  ------ Superposition Simplification Setup
% 3.09/1.05  
% 3.09/1.05  --sup_indices_passive                   []
% 3.09/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_full_bw                           [BwDemod]
% 3.09/1.05  --sup_immed_triv                        [TrivRules]
% 3.09/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_immed_bw_main                     []
% 3.09/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.05  
% 3.09/1.05  ------ Combination Options
% 3.09/1.05  
% 3.09/1.05  --comb_res_mult                         3
% 3.09/1.05  --comb_sup_mult                         2
% 3.09/1.05  --comb_inst_mult                        10
% 3.09/1.05  
% 3.09/1.05  ------ Debug Options
% 3.09/1.05  
% 3.09/1.05  --dbg_backtrace                         false
% 3.09/1.05  --dbg_dump_prop_clauses                 false
% 3.09/1.05  --dbg_dump_prop_clauses_file            -
% 3.09/1.05  --dbg_out_stat                          false
% 3.09/1.05  ------ Parsing...
% 3.09/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/1.05  ------ Proving...
% 3.09/1.05  ------ Problem Properties 
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  clauses                                 38
% 3.09/1.05  conjectures                             21
% 3.09/1.05  EPR                                     19
% 3.09/1.05  Horn                                    30
% 3.09/1.05  unary                                   20
% 3.09/1.05  binary                                  4
% 3.09/1.05  lits                                    131
% 3.09/1.05  lits eq                                 6
% 3.09/1.05  fd_pure                                 0
% 3.09/1.05  fd_pseudo                               0
% 3.09/1.05  fd_cond                                 0
% 3.09/1.05  fd_pseudo_cond                          1
% 3.09/1.05  AC symbols                              0
% 3.09/1.05  
% 3.09/1.05  ------ Schedule dynamic 5 is on 
% 3.09/1.05  
% 3.09/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  ------ 
% 3.09/1.05  Current options:
% 3.09/1.05  ------ 
% 3.09/1.05  
% 3.09/1.05  ------ Input Options
% 3.09/1.05  
% 3.09/1.05  --out_options                           all
% 3.09/1.05  --tptp_safe_out                         true
% 3.09/1.05  --problem_path                          ""
% 3.09/1.05  --include_path                          ""
% 3.09/1.05  --clausifier                            res/vclausify_rel
% 3.09/1.05  --clausifier_options                    --mode clausify
% 3.09/1.05  --stdin                                 false
% 3.09/1.05  --stats_out                             all
% 3.09/1.05  
% 3.09/1.05  ------ General Options
% 3.09/1.05  
% 3.09/1.05  --fof                                   false
% 3.09/1.05  --time_out_real                         305.
% 3.09/1.05  --time_out_virtual                      -1.
% 3.09/1.05  --symbol_type_check                     false
% 3.09/1.05  --clausify_out                          false
% 3.09/1.05  --sig_cnt_out                           false
% 3.09/1.05  --trig_cnt_out                          false
% 3.09/1.05  --trig_cnt_out_tolerance                1.
% 3.09/1.05  --trig_cnt_out_sk_spl                   false
% 3.09/1.05  --abstr_cl_out                          false
% 3.09/1.05  
% 3.09/1.05  ------ Global Options
% 3.09/1.05  
% 3.09/1.05  --schedule                              default
% 3.09/1.05  --add_important_lit                     false
% 3.09/1.05  --prop_solver_per_cl                    1000
% 3.09/1.05  --min_unsat_core                        false
% 3.09/1.05  --soft_assumptions                      false
% 3.09/1.05  --soft_lemma_size                       3
% 3.09/1.05  --prop_impl_unit_size                   0
% 3.09/1.05  --prop_impl_unit                        []
% 3.09/1.05  --share_sel_clauses                     true
% 3.09/1.05  --reset_solvers                         false
% 3.09/1.05  --bc_imp_inh                            [conj_cone]
% 3.09/1.05  --conj_cone_tolerance                   3.
% 3.09/1.05  --extra_neg_conj                        none
% 3.09/1.05  --large_theory_mode                     true
% 3.09/1.05  --prolific_symb_bound                   200
% 3.09/1.05  --lt_threshold                          2000
% 3.09/1.05  --clause_weak_htbl                      true
% 3.09/1.05  --gc_record_bc_elim                     false
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing Options
% 3.09/1.05  
% 3.09/1.05  --preprocessing_flag                    true
% 3.09/1.05  --time_out_prep_mult                    0.1
% 3.09/1.05  --splitting_mode                        input
% 3.09/1.05  --splitting_grd                         true
% 3.09/1.05  --splitting_cvd                         false
% 3.09/1.05  --splitting_cvd_svl                     false
% 3.09/1.05  --splitting_nvd                         32
% 3.09/1.05  --sub_typing                            true
% 3.09/1.05  --prep_gs_sim                           true
% 3.09/1.05  --prep_unflatten                        true
% 3.09/1.05  --prep_res_sim                          true
% 3.09/1.05  --prep_upred                            true
% 3.09/1.05  --prep_sem_filter                       exhaustive
% 3.09/1.05  --prep_sem_filter_out                   false
% 3.09/1.05  --pred_elim                             true
% 3.09/1.05  --res_sim_input                         true
% 3.09/1.05  --eq_ax_congr_red                       true
% 3.09/1.05  --pure_diseq_elim                       true
% 3.09/1.05  --brand_transform                       false
% 3.09/1.05  --non_eq_to_eq                          false
% 3.09/1.05  --prep_def_merge                        true
% 3.09/1.05  --prep_def_merge_prop_impl              false
% 3.09/1.05  --prep_def_merge_mbd                    true
% 3.09/1.05  --prep_def_merge_tr_red                 false
% 3.09/1.05  --prep_def_merge_tr_cl                  false
% 3.09/1.05  --smt_preprocessing                     true
% 3.09/1.05  --smt_ac_axioms                         fast
% 3.09/1.05  --preprocessed_out                      false
% 3.09/1.05  --preprocessed_stats                    false
% 3.09/1.05  
% 3.09/1.05  ------ Abstraction refinement Options
% 3.09/1.05  
% 3.09/1.05  --abstr_ref                             []
% 3.09/1.05  --abstr_ref_prep                        false
% 3.09/1.05  --abstr_ref_until_sat                   false
% 3.09/1.05  --abstr_ref_sig_restrict                funpre
% 3.09/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.05  --abstr_ref_under                       []
% 3.09/1.05  
% 3.09/1.05  ------ SAT Options
% 3.09/1.05  
% 3.09/1.05  --sat_mode                              false
% 3.09/1.05  --sat_fm_restart_options                ""
% 3.09/1.05  --sat_gr_def                            false
% 3.09/1.05  --sat_epr_types                         true
% 3.09/1.05  --sat_non_cyclic_types                  false
% 3.09/1.05  --sat_finite_models                     false
% 3.09/1.05  --sat_fm_lemmas                         false
% 3.09/1.05  --sat_fm_prep                           false
% 3.09/1.05  --sat_fm_uc_incr                        true
% 3.09/1.05  --sat_out_model                         small
% 3.09/1.05  --sat_out_clauses                       false
% 3.09/1.05  
% 3.09/1.05  ------ QBF Options
% 3.09/1.05  
% 3.09/1.05  --qbf_mode                              false
% 3.09/1.05  --qbf_elim_univ                         false
% 3.09/1.05  --qbf_dom_inst                          none
% 3.09/1.05  --qbf_dom_pre_inst                      false
% 3.09/1.05  --qbf_sk_in                             false
% 3.09/1.05  --qbf_pred_elim                         true
% 3.09/1.05  --qbf_split                             512
% 3.09/1.05  
% 3.09/1.05  ------ BMC1 Options
% 3.09/1.05  
% 3.09/1.05  --bmc1_incremental                      false
% 3.09/1.05  --bmc1_axioms                           reachable_all
% 3.09/1.05  --bmc1_min_bound                        0
% 3.09/1.05  --bmc1_max_bound                        -1
% 3.09/1.05  --bmc1_max_bound_default                -1
% 3.09/1.05  --bmc1_symbol_reachability              true
% 3.09/1.05  --bmc1_property_lemmas                  false
% 3.09/1.05  --bmc1_k_induction                      false
% 3.09/1.05  --bmc1_non_equiv_states                 false
% 3.09/1.05  --bmc1_deadlock                         false
% 3.09/1.05  --bmc1_ucm                              false
% 3.09/1.05  --bmc1_add_unsat_core                   none
% 3.09/1.05  --bmc1_unsat_core_children              false
% 3.09/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.05  --bmc1_out_stat                         full
% 3.09/1.05  --bmc1_ground_init                      false
% 3.09/1.05  --bmc1_pre_inst_next_state              false
% 3.09/1.05  --bmc1_pre_inst_state                   false
% 3.09/1.05  --bmc1_pre_inst_reach_state             false
% 3.09/1.05  --bmc1_out_unsat_core                   false
% 3.09/1.05  --bmc1_aig_witness_out                  false
% 3.09/1.05  --bmc1_verbose                          false
% 3.09/1.05  --bmc1_dump_clauses_tptp                false
% 3.09/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.05  --bmc1_dump_file                        -
% 3.09/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.05  --bmc1_ucm_extend_mode                  1
% 3.09/1.05  --bmc1_ucm_init_mode                    2
% 3.09/1.05  --bmc1_ucm_cone_mode                    none
% 3.09/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.05  --bmc1_ucm_relax_model                  4
% 3.09/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.05  --bmc1_ucm_layered_model                none
% 3.09/1.05  --bmc1_ucm_max_lemma_size               10
% 3.09/1.05  
% 3.09/1.05  ------ AIG Options
% 3.09/1.05  
% 3.09/1.05  --aig_mode                              false
% 3.09/1.05  
% 3.09/1.05  ------ Instantiation Options
% 3.09/1.05  
% 3.09/1.05  --instantiation_flag                    true
% 3.09/1.05  --inst_sos_flag                         false
% 3.09/1.05  --inst_sos_phase                        true
% 3.09/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.05  --inst_lit_sel_side                     none
% 3.09/1.05  --inst_solver_per_active                1400
% 3.09/1.05  --inst_solver_calls_frac                1.
% 3.09/1.05  --inst_passive_queue_type               priority_queues
% 3.09/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.05  --inst_passive_queues_freq              [25;2]
% 3.09/1.05  --inst_dismatching                      true
% 3.09/1.05  --inst_eager_unprocessed_to_passive     true
% 3.09/1.05  --inst_prop_sim_given                   true
% 3.09/1.05  --inst_prop_sim_new                     false
% 3.09/1.05  --inst_subs_new                         false
% 3.09/1.05  --inst_eq_res_simp                      false
% 3.09/1.05  --inst_subs_given                       false
% 3.09/1.05  --inst_orphan_elimination               true
% 3.09/1.05  --inst_learning_loop_flag               true
% 3.09/1.05  --inst_learning_start                   3000
% 3.09/1.05  --inst_learning_factor                  2
% 3.09/1.05  --inst_start_prop_sim_after_learn       3
% 3.09/1.05  --inst_sel_renew                        solver
% 3.09/1.05  --inst_lit_activity_flag                true
% 3.09/1.05  --inst_restr_to_given                   false
% 3.09/1.05  --inst_activity_threshold               500
% 3.09/1.05  --inst_out_proof                        true
% 3.09/1.05  
% 3.09/1.05  ------ Resolution Options
% 3.09/1.05  
% 3.09/1.05  --resolution_flag                       false
% 3.09/1.05  --res_lit_sel                           adaptive
% 3.09/1.05  --res_lit_sel_side                      none
% 3.09/1.05  --res_ordering                          kbo
% 3.09/1.05  --res_to_prop_solver                    active
% 3.09/1.05  --res_prop_simpl_new                    false
% 3.09/1.05  --res_prop_simpl_given                  true
% 3.09/1.05  --res_passive_queue_type                priority_queues
% 3.09/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.05  --res_passive_queues_freq               [15;5]
% 3.09/1.05  --res_forward_subs                      full
% 3.09/1.05  --res_backward_subs                     full
% 3.09/1.05  --res_forward_subs_resolution           true
% 3.09/1.05  --res_backward_subs_resolution          true
% 3.09/1.05  --res_orphan_elimination                true
% 3.09/1.05  --res_time_limit                        2.
% 3.09/1.05  --res_out_proof                         true
% 3.09/1.05  
% 3.09/1.05  ------ Superposition Options
% 3.09/1.05  
% 3.09/1.05  --superposition_flag                    true
% 3.09/1.05  --sup_passive_queue_type                priority_queues
% 3.09/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.05  --demod_completeness_check              fast
% 3.09/1.05  --demod_use_ground                      true
% 3.09/1.05  --sup_to_prop_solver                    passive
% 3.09/1.05  --sup_prop_simpl_new                    true
% 3.09/1.05  --sup_prop_simpl_given                  true
% 3.09/1.05  --sup_fun_splitting                     false
% 3.09/1.05  --sup_smt_interval                      50000
% 3.09/1.05  
% 3.09/1.05  ------ Superposition Simplification Setup
% 3.09/1.05  
% 3.09/1.05  --sup_indices_passive                   []
% 3.09/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_full_bw                           [BwDemod]
% 3.09/1.05  --sup_immed_triv                        [TrivRules]
% 3.09/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_immed_bw_main                     []
% 3.09/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.05  
% 3.09/1.05  ------ Combination Options
% 3.09/1.05  
% 3.09/1.05  --comb_res_mult                         3
% 3.09/1.05  --comb_sup_mult                         2
% 3.09/1.05  --comb_inst_mult                        10
% 3.09/1.05  
% 3.09/1.05  ------ Debug Options
% 3.09/1.05  
% 3.09/1.05  --dbg_backtrace                         false
% 3.09/1.05  --dbg_dump_prop_clauses                 false
% 3.09/1.05  --dbg_dump_prop_clauses_file            -
% 3.09/1.05  --dbg_out_stat                          false
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  ------ Proving...
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  % SZS status Theorem for theBenchmark.p
% 3.09/1.05  
% 3.09/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.05  
% 3.09/1.05  fof(f11,axiom,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f28,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f11])).
% 3.09/1.05  
% 3.09/1.05  fof(f29,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(flattening,[],[f28])).
% 3.09/1.05  
% 3.09/1.05  fof(f39,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(nnf_transformation,[],[f29])).
% 3.09/1.05  
% 3.09/1.05  fof(f68,plain,(
% 3.09/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f39])).
% 3.09/1.05  
% 3.09/1.05  fof(f98,plain,(
% 3.09/1.05    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(equality_resolution,[],[f68])).
% 3.09/1.05  
% 3.09/1.05  fof(f10,axiom,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f26,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f10])).
% 3.09/1.05  
% 3.09/1.05  fof(f27,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(flattening,[],[f26])).
% 3.09/1.05  
% 3.09/1.05  fof(f67,plain,(
% 3.09/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f27])).
% 3.09/1.05  
% 3.09/1.05  fof(f96,plain,(
% 3.09/1.05    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(equality_resolution,[],[f67])).
% 3.09/1.05  
% 3.09/1.05  fof(f12,conjecture,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f13,negated_conjecture,(
% 3.09/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.09/1.05    inference(negated_conjecture,[],[f12])).
% 3.09/1.05  
% 3.09/1.05  fof(f30,plain,(
% 3.09/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f13])).
% 3.09/1.05  
% 3.09/1.05  fof(f31,plain,(
% 3.09/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.09/1.05    inference(flattening,[],[f30])).
% 3.09/1.05  
% 3.09/1.05  fof(f40,plain,(
% 3.09/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.09/1.05    inference(nnf_transformation,[],[f31])).
% 3.09/1.05  
% 3.09/1.05  fof(f41,plain,(
% 3.09/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.09/1.05    inference(flattening,[],[f40])).
% 3.09/1.05  
% 3.09/1.05  fof(f49,plain,(
% 3.09/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f48,plain,(
% 3.09/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f47,plain,(
% 3.09/1.05    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f46,plain,(
% 3.09/1.05    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f45,plain,(
% 3.09/1.05    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f44,plain,(
% 3.09/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f43,plain,(
% 3.09/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f42,plain,(
% 3.09/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f50,plain,(
% 3.09/1.05    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.09/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f41,f49,f48,f47,f46,f45,f44,f43,f42])).
% 3.09/1.05  
% 3.09/1.05  fof(f81,plain,(
% 3.09/1.05    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f80,plain,(
% 3.09/1.05    v1_funct_1(sK5)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f9,axiom,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f24,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f9])).
% 3.09/1.05  
% 3.09/1.05  fof(f25,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.09/1.05    inference(flattening,[],[f24])).
% 3.09/1.05  
% 3.09/1.05  fof(f66,plain,(
% 3.09/1.05    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f25])).
% 3.09/1.05  
% 3.09/1.05  fof(f78,plain,(
% 3.09/1.05    ~v2_struct_0(sK4)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f70,plain,(
% 3.09/1.05    ~v2_struct_0(sK1)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f71,plain,(
% 3.09/1.05    v2_pre_topc(sK1)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f72,plain,(
% 3.09/1.05    l1_pre_topc(sK1)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f82,plain,(
% 3.09/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f92,plain,(
% 3.09/1.05    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f90,plain,(
% 3.09/1.05    sK7 = sK8),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f69,plain,(
% 3.09/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f39])).
% 3.09/1.05  
% 3.09/1.05  fof(f97,plain,(
% 3.09/1.05    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(equality_resolution,[],[f69])).
% 3.09/1.05  
% 3.09/1.05  fof(f8,axiom,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f22,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f8])).
% 3.09/1.05  
% 3.09/1.05  fof(f23,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(flattening,[],[f22])).
% 3.09/1.05  
% 3.09/1.05  fof(f35,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(nnf_transformation,[],[f23])).
% 3.09/1.05  
% 3.09/1.05  fof(f36,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(rectify,[],[f35])).
% 3.09/1.05  
% 3.09/1.05  fof(f37,plain,(
% 3.09/1.05    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.09/1.05    introduced(choice_axiom,[])).
% 3.09/1.05  
% 3.09/1.05  fof(f38,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK0(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.09/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.09/1.05  
% 3.09/1.05  fof(f65,plain,(
% 3.09/1.05    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f38])).
% 3.09/1.05  
% 3.09/1.05  fof(f79,plain,(
% 3.09/1.05    m1_pre_topc(sK4,sK2)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f4,axiom,(
% 3.09/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f16,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.09/1.05    inference(ennf_transformation,[],[f4])).
% 3.09/1.05  
% 3.09/1.05  fof(f17,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.09/1.05    inference(flattening,[],[f16])).
% 3.09/1.05  
% 3.09/1.05  fof(f57,plain,(
% 3.09/1.05    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f17])).
% 3.09/1.05  
% 3.09/1.05  fof(f5,axiom,(
% 3.09/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f18,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.09/1.05    inference(ennf_transformation,[],[f5])).
% 3.09/1.05  
% 3.09/1.05  fof(f58,plain,(
% 3.09/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f18])).
% 3.09/1.05  
% 3.09/1.05  fof(f2,axiom,(
% 3.09/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f34,plain,(
% 3.09/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.09/1.05    inference(nnf_transformation,[],[f2])).
% 3.09/1.05  
% 3.09/1.05  fof(f55,plain,(
% 3.09/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f34])).
% 3.09/1.05  
% 3.09/1.05  fof(f1,axiom,(
% 3.09/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f32,plain,(
% 3.09/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.05    inference(nnf_transformation,[],[f1])).
% 3.09/1.05  
% 3.09/1.05  fof(f33,plain,(
% 3.09/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.05    inference(flattening,[],[f32])).
% 3.09/1.05  
% 3.09/1.05  fof(f52,plain,(
% 3.09/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.09/1.05    inference(cnf_transformation,[],[f33])).
% 3.09/1.05  
% 3.09/1.05  fof(f93,plain,(
% 3.09/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/1.05    inference(equality_resolution,[],[f52])).
% 3.09/1.05  
% 3.09/1.05  fof(f6,axiom,(
% 3.09/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f19,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.09/1.05    inference(ennf_transformation,[],[f6])).
% 3.09/1.05  
% 3.09/1.05  fof(f59,plain,(
% 3.09/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f19])).
% 3.09/1.05  
% 3.09/1.05  fof(f7,axiom,(
% 3.09/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.09/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.05  
% 3.09/1.05  fof(f20,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.09/1.05    inference(ennf_transformation,[],[f7])).
% 3.09/1.05  
% 3.09/1.05  fof(f21,plain,(
% 3.09/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.09/1.05    inference(flattening,[],[f20])).
% 3.09/1.05  
% 3.09/1.05  fof(f60,plain,(
% 3.09/1.05    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f21])).
% 3.09/1.05  
% 3.09/1.05  fof(f95,plain,(
% 3.09/1.05    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.09/1.05    inference(equality_resolution,[],[f60])).
% 3.09/1.05  
% 3.09/1.05  fof(f85,plain,(
% 3.09/1.05    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f91,plain,(
% 3.09/1.05    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f53,plain,(
% 3.09/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/1.05    inference(cnf_transformation,[],[f33])).
% 3.09/1.05  
% 3.09/1.05  fof(f51,plain,(
% 3.09/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.09/1.05    inference(cnf_transformation,[],[f33])).
% 3.09/1.05  
% 3.09/1.05  fof(f94,plain,(
% 3.09/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/1.05    inference(equality_resolution,[],[f51])).
% 3.09/1.05  
% 3.09/1.05  fof(f89,plain,(
% 3.09/1.05    r1_tarski(sK6,u1_struct_0(sK3))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f88,plain,(
% 3.09/1.05    r2_hidden(sK7,sK6)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f87,plain,(
% 3.09/1.05    v3_pre_topc(sK6,sK2)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f86,plain,(
% 3.09/1.05    m1_subset_1(sK8,u1_struct_0(sK3))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f84,plain,(
% 3.09/1.05    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f83,plain,(
% 3.09/1.05    m1_pre_topc(sK3,sK4)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f76,plain,(
% 3.09/1.05    ~v2_struct_0(sK3)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f75,plain,(
% 3.09/1.05    l1_pre_topc(sK2)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f74,plain,(
% 3.09/1.05    v2_pre_topc(sK2)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  fof(f73,plain,(
% 3.09/1.05    ~v2_struct_0(sK2)),
% 3.09/1.05    inference(cnf_transformation,[],[f50])).
% 3.09/1.05  
% 3.09/1.05  cnf(c_18,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.09/1.05      | ~ m1_connsp_2(X6,X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/1.05      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f98]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_16,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f96]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_214,plain,
% 3.09/1.05      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.09/1.05      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(global_propositional_subsumption,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_18,c_16]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_215,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5) ),
% 3.09/1.05      inference(renaming,[status(thm)],[c_214]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_30,negated_conjecture,
% 3.09/1.05      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 3.09/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_653,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.09/1.05      | sK5 != X2 ),
% 3.09/1.05      inference(resolution_lifted,[status(thm)],[c_215,c_30]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_654,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ v1_funct_1(sK5)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(unflattening,[status(thm)],[c_653]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_31,negated_conjecture,
% 3.09/1.05      ( v1_funct_1(sK5) ),
% 3.09/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_658,plain,
% 3.09/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(global_propositional_subsumption,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_654,c_31]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_659,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(renaming,[status(thm)],[c_658]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_15,plain,
% 3.09/1.05      ( ~ m1_pre_topc(X0,X1)
% 3.09/1.05      | ~ m1_pre_topc(X2,X0)
% 3.09/1.05      | m1_pre_topc(X2,X1)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_700,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(forward_subsumption_resolution,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_659,c_15]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2709,plain,
% 3.09/1.05      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.09/1.05      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 3.09/1.05      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 3.09/1.05      | m1_pre_topc(X0,X3) != iProver_top
% 3.09/1.05      | m1_pre_topc(X2,X0) != iProver_top
% 3.09/1.05      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.09/1.05      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X2) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X3) = iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top
% 3.09/1.05      | l1_pre_topc(X3) != iProver_top
% 3.09/1.05      | v2_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_pre_topc(X3) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3741,plain,
% 3.09/1.05      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.09/1.05      | m1_pre_topc(X1,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X2) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X2) = iProver_top
% 3.09/1.05      | v2_struct_0(sK4) = iProver_top
% 3.09/1.05      | l1_pre_topc(X0) != iProver_top
% 3.09/1.05      | l1_pre_topc(X2) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) != iProver_top
% 3.09/1.05      | v2_pre_topc(X2) != iProver_top ),
% 3.09/1.05      inference(equality_resolution,[status(thm)],[c_2709]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_33,negated_conjecture,
% 3.09/1.05      ( ~ v2_struct_0(sK4) ),
% 3.09/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_50,plain,
% 3.09/1.05      ( v2_struct_0(sK4) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1790,plain,( X0 = X0 ),theory(equality) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3103,plain,
% 3.09/1.05      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3105,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 3.09/1.05      | ~ r1_tmap_1(sK4,X1,sK5,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,sK4)
% 3.09/1.05      | ~ m1_pre_topc(sK4,X2)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_700]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3106,plain,
% 3.09/1.05      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.09/1.05      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.09/1.05      | m1_pre_topc(X1,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X2) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X2) = iProver_top
% 3.09/1.05      | v2_struct_0(sK4) = iProver_top
% 3.09/1.05      | l1_pre_topc(X0) != iProver_top
% 3.09/1.05      | l1_pre_topc(X2) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) != iProver_top
% 3.09/1.05      | v2_pre_topc(X2) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3105]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4122,plain,
% 3.09/1.05      ( v2_struct_0(X2) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X2) != iProver_top
% 3.09/1.05      | m1_pre_topc(X1,sK4) != iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.09/1.05      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | l1_pre_topc(X0) != iProver_top
% 3.09/1.05      | l1_pre_topc(X2) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) != iProver_top
% 3.09/1.05      | v2_pre_topc(X2) != iProver_top ),
% 3.09/1.05      inference(global_propositional_subsumption,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_3741,c_50,c_3103,c_3106]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4123,plain,
% 3.09/1.05      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.09/1.05      | m1_pre_topc(X1,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X2) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.09/1.05      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X2) = iProver_top
% 3.09/1.05      | l1_pre_topc(X0) != iProver_top
% 3.09/1.05      | l1_pre_topc(X2) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) != iProver_top
% 3.09/1.05      | v2_pre_topc(X2) != iProver_top ),
% 3.09/1.05      inference(renaming,[status(thm)],[c_4122]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4143,plain,
% 3.09/1.05      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.09/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(sK1) = iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top
% 3.09/1.05      | l1_pre_topc(sK1) != iProver_top
% 3.09/1.05      | v2_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK1) != iProver_top ),
% 3.09/1.05      inference(equality_resolution,[status(thm)],[c_4123]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_41,negated_conjecture,
% 3.09/1.05      ( ~ v2_struct_0(sK1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_42,plain,
% 3.09/1.05      ( v2_struct_0(sK1) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_40,negated_conjecture,
% 3.09/1.05      ( v2_pre_topc(sK1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_43,plain,
% 3.09/1.05      ( v2_pre_topc(sK1) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_39,negated_conjecture,
% 3.09/1.05      ( l1_pre_topc(sK1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f72]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_44,plain,
% 3.09/1.05      ( l1_pre_topc(sK1) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_29,negated_conjecture,
% 3.09/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 3.09/1.05      inference(cnf_transformation,[],[f82]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_54,plain,
% 3.09/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_7788,plain,
% 3.09/1.05      ( v2_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.09/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top ),
% 3.09/1.05      inference(global_propositional_subsumption,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_4143,c_42,c_43,c_44,c_54]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_7789,plain,
% 3.09/1.05      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.09/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.09/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | v2_struct_0(X1) = iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_pre_topc(X1) != iProver_top ),
% 3.09/1.05      inference(renaming,[status(thm)],[c_7788]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_19,negated_conjecture,
% 3.09/1.05      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.09/1.05      inference(cnf_transformation,[],[f92]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2729,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_21,negated_conjecture,
% 3.09/1.05      ( sK7 = sK8 ),
% 3.09/1.05      inference(cnf_transformation,[],[f90]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2818,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.09/1.05      inference(light_normalisation,[status(thm)],[c_2729,c_21]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_7804,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.09/1.05      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.09/1.05      | v2_struct_0(sK2) = iProver_top
% 3.09/1.05      | v2_struct_0(sK3) = iProver_top
% 3.09/1.05      | l1_pre_topc(sK2) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK2) != iProver_top ),
% 3.09/1.05      inference(superposition,[status(thm)],[c_7789,c_2818]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_17,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.09/1.05      | ~ m1_connsp_2(X6,X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/1.05      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_719,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.09/1.05      | ~ m1_connsp_2(X6,X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X5)
% 3.09/1.05      | ~ m1_pre_topc(X4,X0)
% 3.09/1.05      | ~ m1_pre_topc(X4,X5)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.09/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/1.05      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.09/1.05      | ~ v1_funct_1(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X5)
% 3.09/1.05      | v2_struct_0(X4)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X5)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X5)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.09/1.05      | sK5 != X2 ),
% 3.09/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_720,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.09/1.05      | ~ v1_funct_1(sK5)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(unflattening,[status(thm)],[c_719]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_724,plain,
% 3.09/1.05      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 3.09/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(global_propositional_subsumption,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_720,c_31]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_725,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(renaming,[status(thm)],[c_724]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_772,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.09/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 3.09/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 3.09/1.05      | ~ m1_pre_topc(X3,X2)
% 3.09/1.05      | ~ m1_pre_topc(X0,X3)
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.09/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.09/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(X3)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.09/1.05      inference(forward_subsumption_resolution,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_725,c_15]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3104,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 3.09/1.05      | r1_tmap_1(sK4,X1,sK5,X3)
% 3.09/1.05      | ~ m1_connsp_2(X4,sK4,X3)
% 3.09/1.05      | ~ m1_pre_topc(X0,sK4)
% 3.09/1.05      | ~ m1_pre_topc(sK4,X2)
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.09/1.05      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.09/1.05      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_772]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3779,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.09/1.05      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(X2,X0,sK4,sK3,sK5),X1)
% 3.09/1.05      | ~ m1_connsp_2(X3,sK4,X1)
% 3.09/1.05      | ~ m1_pre_topc(sK4,X2)
% 3.09/1.05      | ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.09/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.09/1.05      | ~ r1_tarski(X3,u1_struct_0(sK3))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(X2)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | v2_struct_0(sK3)
% 3.09/1.05      | ~ l1_pre_topc(X0)
% 3.09/1.05      | ~ l1_pre_topc(X2)
% 3.09/1.05      | ~ v2_pre_topc(X0)
% 3.09/1.05      | ~ v2_pre_topc(X2)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3104]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3820,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.09/1.05      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),X1)
% 3.09/1.05      | ~ m1_connsp_2(X2,sK4,X1)
% 3.09/1.05      | ~ m1_pre_topc(sK4,sK2)
% 3.09/1.05      | ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.09/1.05      | ~ r1_tarski(X2,u1_struct_0(sK3))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | v2_struct_0(sK2)
% 3.09/1.05      | v2_struct_0(sK3)
% 3.09/1.05      | ~ l1_pre_topc(X0)
% 3.09/1.05      | ~ l1_pre_topc(sK2)
% 3.09/1.05      | ~ v2_pre_topc(X0)
% 3.09/1.05      | ~ v2_pre_topc(sK2)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3779]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4311,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,X0,sK5,sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7)
% 3.09/1.05      | ~ m1_connsp_2(X1,sK4,sK7)
% 3.09/1.05      | ~ m1_pre_topc(sK4,sK2)
% 3.09/1.05      | ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.09/1.05      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | v2_struct_0(sK2)
% 3.09/1.05      | v2_struct_0(sK3)
% 3.09/1.05      | ~ l1_pre_topc(X0)
% 3.09/1.05      | ~ l1_pre_topc(sK2)
% 3.09/1.05      | ~ v2_pre_topc(X0)
% 3.09/1.05      | ~ v2_pre_topc(sK2)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3820]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6441,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,X0,sK5,sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7)
% 3.09/1.05      | ~ m1_connsp_2(sK6,sK4,sK7)
% 3.09/1.05      | ~ m1_pre_topc(sK4,sK2)
% 3.09/1.05      | ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.09/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.09/1.05      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 3.09/1.05      | v2_struct_0(X0)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | v2_struct_0(sK2)
% 3.09/1.05      | v2_struct_0(sK3)
% 3.09/1.05      | ~ l1_pre_topc(X0)
% 3.09/1.05      | ~ l1_pre_topc(sK2)
% 3.09/1.05      | ~ v2_pre_topc(X0)
% 3.09/1.05      | ~ v2_pre_topc(sK2)
% 3.09/1.05      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_4311]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6442,plain,
% 3.09/1.05      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.09/1.05      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.09/1.05      | r1_tmap_1(sK4,X0,sK5,sK7) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,X0,k3_tmap_1(sK2,X0,sK4,sK3,sK5),sK7) != iProver_top
% 3.09/1.05      | m1_connsp_2(sK6,sK4,sK7) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.09/1.05      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 3.09/1.05      | v2_struct_0(X0) = iProver_top
% 3.09/1.05      | v2_struct_0(sK4) = iProver_top
% 3.09/1.05      | v2_struct_0(sK2) = iProver_top
% 3.09/1.05      | v2_struct_0(sK3) = iProver_top
% 3.09/1.05      | l1_pre_topc(X0) != iProver_top
% 3.09/1.05      | l1_pre_topc(sK2) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK2) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_6441]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6444,plain,
% 3.09/1.05      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.09/1.05      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.09/1.05      | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top
% 3.09/1.05      | m1_connsp_2(sK6,sK4,sK7) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.09/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.09/1.05      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 3.09/1.05      | v2_struct_0(sK4) = iProver_top
% 3.09/1.05      | v2_struct_0(sK2) = iProver_top
% 3.09/1.05      | v2_struct_0(sK1) = iProver_top
% 3.09/1.05      | v2_struct_0(sK3) = iProver_top
% 3.09/1.05      | l1_pre_topc(sK2) != iProver_top
% 3.09/1.05      | l1_pre_topc(sK1) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK2) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK1) != iProver_top ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_6442]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_10,plain,
% 3.09/1.05      ( m1_connsp_2(X0,X1,X2)
% 3.09/1.05      | ~ v3_pre_topc(X3,X1)
% 3.09/1.05      | ~ r2_hidden(X2,X3)
% 3.09/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/1.05      | ~ r1_tarski(X3,X0)
% 3.09/1.05      | v2_struct_0(X1)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f65]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4330,plain,
% 3.09/1.05      ( m1_connsp_2(X0,sK4,X1)
% 3.09/1.05      | ~ v3_pre_topc(sK6,sK4)
% 3.09/1.05      | ~ r2_hidden(X1,sK6)
% 3.09/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ r1_tarski(sK6,X0)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | ~ l1_pre_topc(sK4)
% 3.09/1.05      | ~ v2_pre_topc(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_5674,plain,
% 3.09/1.05      ( m1_connsp_2(X0,sK4,sK7)
% 3.09/1.05      | ~ v3_pre_topc(sK6,sK4)
% 3.09/1.05      | ~ r2_hidden(sK7,sK6)
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.09/1.05      | ~ r1_tarski(sK6,X0)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | ~ l1_pre_topc(sK4)
% 3.09/1.05      | ~ v2_pre_topc(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_4330]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6188,plain,
% 3.09/1.05      ( m1_connsp_2(sK6,sK4,sK7)
% 3.09/1.05      | ~ v3_pre_topc(sK6,sK4)
% 3.09/1.05      | ~ r2_hidden(sK7,sK6)
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.09/1.05      | ~ r1_tarski(sK6,sK6)
% 3.09/1.05      | v2_struct_0(sK4)
% 3.09/1.05      | ~ l1_pre_topc(sK4)
% 3.09/1.05      | ~ v2_pre_topc(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_5674]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6189,plain,
% 3.09/1.05      ( m1_connsp_2(sK6,sK4,sK7) = iProver_top
% 3.09/1.05      | v3_pre_topc(sK6,sK4) != iProver_top
% 3.09/1.05      | r2_hidden(sK7,sK6) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 3.09/1.05      | r1_tarski(sK6,sK6) != iProver_top
% 3.09/1.05      | v2_struct_0(sK4) = iProver_top
% 3.09/1.05      | l1_pre_topc(sK4) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK4) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_6188]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4448,plain,
% 3.09/1.05      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1803,plain,
% 3.09/1.05      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | r1_tmap_1(X4,X5,X6,X7)
% 3.09/1.05      | X4 != X0
% 3.09/1.05      | X5 != X1
% 3.09/1.05      | X6 != X2
% 3.09/1.05      | X7 != X3 ),
% 3.09/1.05      theory(equality) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3278,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,X2,X3)
% 3.09/1.05      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 3.09/1.05      | X2 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | X3 != sK8
% 3.09/1.05      | X1 != sK1
% 3.09/1.05      | X0 != sK3 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1803]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3590,plain,
% 3.09/1.05      ( r1_tmap_1(X0,X1,X2,sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 3.09/1.05      | X2 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | X1 != sK1
% 3.09/1.05      | X0 != sK3
% 3.09/1.05      | sK7 != sK8 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3278]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4099,plain,
% 3.09/1.05      ( r1_tmap_1(sK3,X0,X1,sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 3.09/1.05      | X1 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | X0 != sK1
% 3.09/1.05      | sK7 != sK8
% 3.09/1.05      | sK3 != sK3 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3590]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4447,plain,
% 3.09/1.05      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
% 3.09/1.05      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 3.09/1.05      | X0 != sK1
% 3.09/1.05      | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | sK7 != sK8
% 3.09/1.05      | sK3 != sK3 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_4099]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4449,plain,
% 3.09/1.05      ( X0 != sK1
% 3.09/1.05      | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | sK7 != sK8
% 3.09/1.05      | sK3 != sK3
% 3.09/1.05      | r1_tmap_1(sK3,X0,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_4447]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4451,plain,
% 3.09/1.05      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 3.09/1.05      | sK7 != sK8
% 3.09/1.05      | sK1 != sK1
% 3.09/1.05      | sK3 != sK3
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_4449]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_32,negated_conjecture,
% 3.09/1.05      ( m1_pre_topc(sK4,sK2) ),
% 3.09/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2719,plain,
% 3.09/1.05      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_6,plain,
% 3.09/1.05      ( ~ m1_pre_topc(X0,X1)
% 3.09/1.05      | ~ l1_pre_topc(X1)
% 3.09/1.05      | ~ v2_pre_topc(X1)
% 3.09/1.05      | v2_pre_topc(X0) ),
% 3.09/1.05      inference(cnf_transformation,[],[f57]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2739,plain,
% 3.09/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_pre_topc(X1) != iProver_top
% 3.09/1.05      | v2_pre_topc(X0) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_4371,plain,
% 3.09/1.05      ( l1_pre_topc(sK2) != iProver_top
% 3.09/1.05      | v2_pre_topc(sK4) = iProver_top
% 3.09/1.05      | v2_pre_topc(sK2) != iProver_top ),
% 3.09/1.05      inference(superposition,[status(thm)],[c_2719,c_2739]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_7,plain,
% 3.09/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.09/1.05      inference(cnf_transformation,[],[f58]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2738,plain,
% 3.09/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 3.09/1.05      | l1_pre_topc(X1) != iProver_top
% 3.09/1.05      | l1_pre_topc(X0) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3887,plain,
% 3.09/1.05      ( l1_pre_topc(sK4) = iProver_top
% 3.09/1.05      | l1_pre_topc(sK2) != iProver_top ),
% 3.09/1.05      inference(superposition,[status(thm)],[c_2719,c_2738]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3702,plain,
% 3.09/1.05      ( sK3 = sK3 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3,plain,
% 3.09/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f55]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3288,plain,
% 3.09/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) | ~ r1_tarski(sK6,X0) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3620,plain,
% 3.09/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.09/1.05      | ~ r1_tarski(sK6,u1_struct_0(sK3)) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3288]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3621,plain,
% 3.09/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.09/1.05      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3620]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1,plain,
% 3.09/1.05      ( r1_tarski(X0,X0) ),
% 3.09/1.05      inference(cnf_transformation,[],[f93]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3615,plain,
% 3.09/1.05      ( r1_tarski(sK6,sK6) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3618,plain,
% 3.09/1.05      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3615]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3473,plain,
% 3.09/1.05      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1794,plain,
% 3.09/1.05      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.09/1.05      theory(equality) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3169,plain,
% 3.09/1.05      ( m1_subset_1(X0,X1)
% 3.09/1.05      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.09/1.05      | X1 != u1_struct_0(sK3)
% 3.09/1.05      | X0 != sK8 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1794]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3402,plain,
% 3.09/1.05      ( m1_subset_1(sK7,X0)
% 3.09/1.05      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.09/1.05      | X0 != u1_struct_0(sK3)
% 3.09/1.05      | sK7 != sK8 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3169]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3472,plain,
% 3.09/1.05      ( m1_subset_1(sK7,u1_struct_0(sK3))
% 3.09/1.05      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 3.09/1.05      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.09/1.05      | sK7 != sK8 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3402]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3474,plain,
% 3.09/1.05      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.09/1.05      | sK7 != sK8
% 3.09/1.05      | m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top
% 3.09/1.05      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3472]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_8,plain,
% 3.09/1.05      ( ~ m1_pre_topc(X0,X1)
% 3.09/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/1.05      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/1.05      | ~ l1_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f59]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3130,plain,
% 3.09/1.05      ( ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.09/1.05      | ~ l1_pre_topc(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3339,plain,
% 3.09/1.05      ( ~ m1_pre_topc(sK3,sK4)
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.09/1.05      | ~ l1_pre_topc(sK4) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3130]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3342,plain,
% 3.09/1.05      ( m1_pre_topc(sK3,sK4) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.09/1.05      | l1_pre_topc(sK4) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3339]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_9,plain,
% 3.09/1.05      ( ~ v3_pre_topc(X0,X1)
% 3.09/1.05      | v3_pre_topc(X0,X2)
% 3.09/1.05      | ~ m1_pre_topc(X2,X1)
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.09/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/1.05      | ~ l1_pre_topc(X1) ),
% 3.09/1.05      inference(cnf_transformation,[],[f95]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3206,plain,
% 3.09/1.05      ( v3_pre_topc(sK6,X0)
% 3.09/1.05      | ~ v3_pre_topc(sK6,sK2)
% 3.09/1.05      | ~ m1_pre_topc(X0,sK2)
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.09/1.05      | ~ l1_pre_topc(sK2) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_9]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3338,plain,
% 3.09/1.05      ( v3_pre_topc(sK6,sK4)
% 3.09/1.05      | ~ v3_pre_topc(sK6,sK2)
% 3.09/1.05      | ~ m1_pre_topc(sK4,sK2)
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.09/1.05      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.09/1.05      | ~ l1_pre_topc(sK2) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_3206]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_3340,plain,
% 3.09/1.05      ( v3_pre_topc(sK6,sK4) = iProver_top
% 3.09/1.05      | v3_pre_topc(sK6,sK2) != iProver_top
% 3.09/1.05      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.09/1.05      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.09/1.05      | l1_pre_topc(sK2) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_3338]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_26,negated_conjecture,
% 3.09/1.05      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.09/1.05      inference(cnf_transformation,[],[f85]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2723,plain,
% 3.09/1.05      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2776,plain,
% 3.09/1.05      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.09/1.05      inference(light_normalisation,[status(thm)],[c_2723,c_21]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_20,negated_conjecture,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.09/1.05      inference(cnf_transformation,[],[f91]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2728,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2807,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.09/1.05      inference(light_normalisation,[status(thm)],[c_2728,c_21]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1799,plain,
% 3.09/1.05      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.09/1.05      theory(equality) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_1812,plain,
% 3.09/1.05      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_1799]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_0,plain,
% 3.09/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.09/1.05      inference(cnf_transformation,[],[f53]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_107,plain,
% 3.09/1.05      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_2,plain,
% 3.09/1.05      ( r1_tarski(X0,X0) ),
% 3.09/1.05      inference(cnf_transformation,[],[f94]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_103,plain,
% 3.09/1.05      ( r1_tarski(sK1,sK1) ),
% 3.09/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_63,plain,
% 3.09/1.05      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.09/1.05      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_22,negated_conjecture,
% 3.09/1.05      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 3.09/1.05      inference(cnf_transformation,[],[f89]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_61,plain,
% 3.09/1.05      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_23,negated_conjecture,
% 3.09/1.05      ( r2_hidden(sK7,sK6) ),
% 3.09/1.05      inference(cnf_transformation,[],[f88]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_60,plain,
% 3.09/1.05      ( r2_hidden(sK7,sK6) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_24,negated_conjecture,
% 3.09/1.05      ( v3_pre_topc(sK6,sK2) ),
% 3.09/1.05      inference(cnf_transformation,[],[f87]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_59,plain,
% 3.09/1.05      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_25,negated_conjecture,
% 3.09/1.05      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 3.09/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_58,plain,
% 3.09/1.05      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_57,plain,
% 3.09/1.05      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_27,negated_conjecture,
% 3.09/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.09/1.05      inference(cnf_transformation,[],[f84]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_56,plain,
% 3.09/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_28,negated_conjecture,
% 3.09/1.05      ( m1_pre_topc(sK3,sK4) ),
% 3.09/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_55,plain,
% 3.09/1.05      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_51,plain,
% 3.09/1.05      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_35,negated_conjecture,
% 3.09/1.05      ( ~ v2_struct_0(sK3) ),
% 3.09/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_48,plain,
% 3.09/1.05      ( v2_struct_0(sK3) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_36,negated_conjecture,
% 3.09/1.05      ( l1_pre_topc(sK2) ),
% 3.09/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_47,plain,
% 3.09/1.05      ( l1_pre_topc(sK2) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_37,negated_conjecture,
% 3.09/1.05      ( v2_pre_topc(sK2) ),
% 3.09/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_46,plain,
% 3.09/1.05      ( v2_pre_topc(sK2) = iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_38,negated_conjecture,
% 3.09/1.05      ( ~ v2_struct_0(sK2) ),
% 3.09/1.05      inference(cnf_transformation,[],[f73]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(c_45,plain,
% 3.09/1.05      ( v2_struct_0(sK2) != iProver_top ),
% 3.09/1.05      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.09/1.05  
% 3.09/1.05  cnf(contradiction,plain,
% 3.09/1.05      ( $false ),
% 3.09/1.05      inference(minisat,
% 3.09/1.05                [status(thm)],
% 3.09/1.05                [c_7804,c_6444,c_6189,c_4448,c_4451,c_4371,c_3887,c_3702,
% 3.09/1.05                 c_3621,c_3618,c_3473,c_3474,c_3342,c_3340,c_3103,c_2776,
% 3.09/1.05                 c_2807,c_1812,c_107,c_103,c_63,c_21,c_61,c_60,c_59,c_58,
% 3.09/1.05                 c_57,c_56,c_55,c_54,c_51,c_50,c_48,c_47,c_46,c_45,c_44,
% 3.09/1.05                 c_43,c_42]) ).
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.05  
% 3.09/1.05  ------                               Statistics
% 3.09/1.05  
% 3.09/1.05  ------ General
% 3.09/1.05  
% 3.09/1.05  abstr_ref_over_cycles:                  0
% 3.09/1.05  abstr_ref_under_cycles:                 0
% 3.09/1.05  gc_basic_clause_elim:                   0
% 3.09/1.05  forced_gc_time:                         0
% 3.09/1.05  parsing_time:                           0.012
% 3.09/1.05  unif_index_cands_time:                  0.
% 3.09/1.05  unif_index_add_time:                    0.
% 3.09/1.05  orderings_time:                         0.
% 3.09/1.05  out_proof_time:                         0.013
% 3.09/1.05  total_time:                             0.296
% 3.09/1.05  num_of_symbols:                         56
% 3.09/1.05  num_of_terms:                           4082
% 3.09/1.05  
% 3.09/1.05  ------ Preprocessing
% 3.09/1.05  
% 3.09/1.05  num_of_splits:                          0
% 3.09/1.05  num_of_split_atoms:                     0
% 3.09/1.05  num_of_reused_defs:                     0
% 3.09/1.05  num_eq_ax_congr_red:                    18
% 3.09/1.05  num_of_sem_filtered_clauses:            1
% 3.09/1.05  num_of_subtypes:                        0
% 3.09/1.05  monotx_restored_types:                  0
% 3.09/1.05  sat_num_of_epr_types:                   0
% 3.09/1.05  sat_num_of_non_cyclic_types:            0
% 3.09/1.05  sat_guarded_non_collapsed_types:        0
% 3.09/1.05  num_pure_diseq_elim:                    0
% 3.09/1.05  simp_replaced_by:                       0
% 3.09/1.05  res_preprocessed:                       186
% 3.09/1.05  prep_upred:                             0
% 3.09/1.05  prep_unflattend:                        25
% 3.09/1.05  smt_new_axioms:                         0
% 3.09/1.05  pred_elim_cands:                        10
% 3.09/1.05  pred_elim:                              2
% 3.09/1.05  pred_elim_cl:                           3
% 3.09/1.05  pred_elim_cycles:                       6
% 3.09/1.05  merged_defs:                            16
% 3.09/1.05  merged_defs_ncl:                        0
% 3.09/1.05  bin_hyper_res:                          16
% 3.09/1.05  prep_cycles:                            4
% 3.09/1.05  pred_elim_time:                         0.027
% 3.09/1.05  splitting_time:                         0.
% 3.09/1.05  sem_filter_time:                        0.
% 3.09/1.05  monotx_time:                            0.001
% 3.09/1.05  subtype_inf_time:                       0.
% 3.09/1.05  
% 3.09/1.05  ------ Problem properties
% 3.09/1.05  
% 3.09/1.05  clauses:                                38
% 3.09/1.05  conjectures:                            21
% 3.09/1.05  epr:                                    19
% 3.09/1.05  horn:                                   30
% 3.09/1.05  ground:                                 21
% 3.09/1.05  unary:                                  20
% 3.09/1.05  binary:                                 4
% 3.09/1.05  lits:                                   131
% 3.09/1.05  lits_eq:                                6
% 3.09/1.05  fd_pure:                                0
% 3.09/1.05  fd_pseudo:                              0
% 3.09/1.05  fd_cond:                                0
% 3.09/1.05  fd_pseudo_cond:                         1
% 3.09/1.05  ac_symbols:                             0
% 3.09/1.05  
% 3.09/1.05  ------ Propositional Solver
% 3.09/1.05  
% 3.09/1.05  prop_solver_calls:                      28
% 3.09/1.05  prop_fast_solver_calls:                 2224
% 3.09/1.05  smt_solver_calls:                       0
% 3.09/1.05  smt_fast_solver_calls:                  0
% 3.09/1.05  prop_num_of_clauses:                    2088
% 3.09/1.05  prop_preprocess_simplified:             6622
% 3.09/1.05  prop_fo_subsumed:                       65
% 3.09/1.05  prop_solver_time:                       0.
% 3.09/1.05  smt_solver_time:                        0.
% 3.09/1.05  smt_fast_solver_time:                   0.
% 3.09/1.05  prop_fast_solver_time:                  0.
% 3.09/1.05  prop_unsat_core_time:                   0.
% 3.09/1.05  
% 3.09/1.05  ------ QBF
% 3.09/1.05  
% 3.09/1.05  qbf_q_res:                              0
% 3.09/1.05  qbf_num_tautologies:                    0
% 3.09/1.05  qbf_prep_cycles:                        0
% 3.09/1.05  
% 3.09/1.05  ------ BMC1
% 3.09/1.05  
% 3.09/1.05  bmc1_current_bound:                     -1
% 3.09/1.05  bmc1_last_solved_bound:                 -1
% 3.09/1.05  bmc1_unsat_core_size:                   -1
% 3.09/1.05  bmc1_unsat_core_parents_size:           -1
% 3.09/1.05  bmc1_merge_next_fun:                    0
% 3.09/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.05  
% 3.09/1.05  ------ Instantiation
% 3.09/1.05  
% 3.09/1.05  inst_num_of_clauses:                    560
% 3.09/1.05  inst_num_in_passive:                    28
% 3.09/1.05  inst_num_in_active:                     420
% 3.09/1.05  inst_num_in_unprocessed:                117
% 3.09/1.05  inst_num_of_loops:                      480
% 3.09/1.05  inst_num_of_learning_restarts:          0
% 3.09/1.05  inst_num_moves_active_passive:          55
% 3.09/1.05  inst_lit_activity:                      0
% 3.09/1.05  inst_lit_activity_moves:                0
% 3.09/1.05  inst_num_tautologies:                   0
% 3.09/1.05  inst_num_prop_implied:                  0
% 3.09/1.05  inst_num_existing_simplified:           0
% 3.09/1.05  inst_num_eq_res_simplified:             0
% 3.09/1.05  inst_num_child_elim:                    0
% 3.09/1.05  inst_num_of_dismatching_blockings:      132
% 3.09/1.05  inst_num_of_non_proper_insts:           929
% 3.09/1.05  inst_num_of_duplicates:                 0
% 3.09/1.05  inst_inst_num_from_inst_to_res:         0
% 3.09/1.05  inst_dismatching_checking_time:         0.
% 3.09/1.05  
% 3.09/1.05  ------ Resolution
% 3.09/1.05  
% 3.09/1.05  res_num_of_clauses:                     0
% 3.09/1.05  res_num_in_passive:                     0
% 3.09/1.05  res_num_in_active:                      0
% 3.09/1.05  res_num_of_loops:                       190
% 3.09/1.05  res_forward_subset_subsumed:            123
% 3.09/1.05  res_backward_subset_subsumed:           12
% 3.09/1.05  res_forward_subsumed:                   0
% 3.09/1.05  res_backward_subsumed:                  0
% 3.09/1.05  res_forward_subsumption_resolution:     11
% 3.09/1.05  res_backward_subsumption_resolution:    0
% 3.09/1.05  res_clause_to_clause_subsumption:       681
% 3.09/1.05  res_orphan_elimination:                 0
% 3.09/1.05  res_tautology_del:                      104
% 3.09/1.05  res_num_eq_res_simplified:              0
% 3.09/1.05  res_num_sel_changes:                    0
% 3.09/1.05  res_moves_from_active_to_pass:          0
% 3.09/1.05  
% 3.09/1.05  ------ Superposition
% 3.09/1.05  
% 3.09/1.05  sup_time_total:                         0.
% 3.09/1.05  sup_time_generating:                    0.
% 3.09/1.05  sup_time_sim_full:                      0.
% 3.09/1.05  sup_time_sim_immed:                     0.
% 3.09/1.05  
% 3.09/1.05  sup_num_of_clauses:                     121
% 3.09/1.05  sup_num_in_active:                      95
% 3.09/1.05  sup_num_in_passive:                     26
% 3.09/1.05  sup_num_of_loops:                       94
% 3.09/1.05  sup_fw_superposition:                   87
% 3.09/1.05  sup_bw_superposition:                   33
% 3.09/1.05  sup_immediate_simplified:               24
% 3.09/1.05  sup_given_eliminated:                   0
% 3.09/1.05  comparisons_done:                       0
% 3.09/1.05  comparisons_avoided:                    0
% 3.09/1.05  
% 3.09/1.05  ------ Simplifications
% 3.09/1.05  
% 3.09/1.05  
% 3.09/1.05  sim_fw_subset_subsumed:                 10
% 3.09/1.05  sim_bw_subset_subsumed:                 0
% 3.09/1.05  sim_fw_subsumed:                        11
% 3.09/1.05  sim_bw_subsumed:                        3
% 3.09/1.05  sim_fw_subsumption_res:                 4
% 3.09/1.05  sim_bw_subsumption_res:                 0
% 3.09/1.05  sim_tautology_del:                      2
% 3.09/1.05  sim_eq_tautology_del:                   1
% 3.09/1.05  sim_eq_res_simp:                        0
% 3.09/1.05  sim_fw_demodulated:                     0
% 3.09/1.05  sim_bw_demodulated:                     0
% 3.09/1.05  sim_light_normalised:                   4
% 3.09/1.05  sim_joinable_taut:                      0
% 3.09/1.05  sim_joinable_simp:                      0
% 3.09/1.05  sim_ac_normalised:                      0
% 3.09/1.05  sim_smt_subsumption:                    0
% 3.09/1.05  
%------------------------------------------------------------------------------
