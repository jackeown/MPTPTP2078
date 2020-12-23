%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:23 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 649 expanded)
%              Number of clauses        :  103 ( 136 expanded)
%              Number of leaves         :   19 ( 255 expanded)
%              Depth                    :   20
%              Number of atoms          : 1517 (12147 expanded)
%              Number of equality atoms :  133 ( 767 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   46 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f32])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f33,f40,f39,f38,f37,f36,f35,f34])).

fof(f65,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f67,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f81])).

cnf(c_9,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_162,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
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
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_9])).

cnf(c_163,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_162])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_531,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_163,c_21])).

cnf(c_532,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_536,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_22])).

cnf(c_537,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
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
    inference(renaming,[status(thm)],[c_536])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_578,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
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
    inference(forward_subsumption_resolution,[status(thm)],[c_537,c_8])).

cnf(c_1226,plain,
    ( r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,X3_49,X0_49,sK4),X0_50)
    | ~ r1_tmap_1(X3_49,X1_49,sK4,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X3_49))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | v2_struct_0(X3_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | u1_struct_0(X3_49) != u1_struct_0(sK3)
    | u1_struct_0(X1_49) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_578])).

cnf(c_2130,plain,
    ( r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,sK3,X0_49,sK4),X0_50)
    | ~ r1_tmap_1(sK3,X1_49,sK4,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_49))))
    | ~ m1_pre_topc(X0_49,sK3)
    | ~ m1_pre_topc(sK3,X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | u1_struct_0(X1_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_2463,plain,
    ( ~ r1_tmap_1(sK3,X0_49,sK4,X0_50)
    | r1_tmap_1(sK2,X0_49,k3_tmap_1(X1_49,X0_49,sK3,sK2,sK4),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,X1_49)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X0_49)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_2850,plain,
    ( ~ r1_tmap_1(sK3,X0_49,sK4,X0_50)
    | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2463])).

cnf(c_3319,plain,
    ( ~ r1_tmap_1(sK3,X0_49,sK4,sK6)
    | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_3321,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f80])).

cnf(c_597,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_598,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_602,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
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
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_22])).

cnf(c_603,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
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
    inference(renaming,[status(thm)],[c_602])).

cnf(c_646,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_603,c_8])).

cnf(c_1225,plain,
    ( ~ r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,X3_49,X0_49,sK4),X0_50)
    | r1_tmap_1(X3_49,X1_49,sK4,X0_50)
    | ~ v1_tsep_1(X0_49,X3_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(X3_49))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | v2_struct_0(X3_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | u1_struct_0(X3_49) != u1_struct_0(sK3)
    | u1_struct_0(X1_49) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(c_2129,plain,
    ( ~ r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,sK3,X0_49,sK4),X0_50)
    | r1_tmap_1(sK3,X1_49,sK4,X0_50)
    | ~ v1_tsep_1(X0_49,sK3)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_49))))
    | ~ m1_pre_topc(X0_49,sK3)
    | ~ m1_pre_topc(sK3,X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | u1_struct_0(X1_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_2621,plain,
    ( r1_tmap_1(sK3,X0_49,sK4,X0_50)
    | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(X1_49,X0_49,sK3,sK2,sK4),X0_50)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,X1_49)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X0_49)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_2920,plain,
    ( r1_tmap_1(sK3,X0_49,sK4,X0_50)
    | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),X0_50)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_3279,plain,
    ( r1_tmap_1(sK3,X0_49,sK4,sK5)
    | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK5)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2920])).

cnf(c_3281,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3279])).

cnf(c_1254,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_3071,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1260,plain,
    ( ~ r1_tmap_1(X0_49,X1_49,X0_50,X1_50)
    | r1_tmap_1(X0_49,X1_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2209,plain,
    ( r1_tmap_1(sK2,sK0,X0_50,X1_50)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | X0_50 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_50 != sK6 ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_2384,plain,
    ( r1_tmap_1(sK2,sK0,X0_50,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | X0_50 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2995,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2711,plain,
    ( k3_tmap_1(X0_49,X1_49,sK3,sK2,sK4) = k3_tmap_1(X0_49,X1_49,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_2994,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2711])).

cnf(c_2899,plain,
    ( ~ r1_tmap_1(sK3,X0_49,sK4,sK5)
    | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_49) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_2901,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2899])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1251,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2398,plain,
    ( ~ m1_pre_topc(sK3,X0_49)
    | ~ l1_pre_topc(X0_49)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_2558,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_3,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1249,plain,
    ( ~ v3_pre_topc(X0_50,X0_49)
    | v3_pre_topc(X0_50,X1_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ m1_pre_topc(X1_49,X0_49)
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2239,plain,
    ( v3_pre_topc(u1_struct_0(sK2),X0_49)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0_49,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_2419,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_2358,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1257,plain,
    ( ~ m1_subset_1(X0_50,X1_50)
    | m1_subset_1(X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2194,plain,
    ( m1_subset_1(X0_50,X1_50)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | X1_50 != u1_struct_0(sK2)
    | X0_50 != sK6 ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_2300,plain,
    ( m1_subset_1(sK5,X0_50)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | X0_50 != u1_struct_0(sK2)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_2357,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1237,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1868,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1252,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v2_pre_topc(X1_49)
    | v2_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1854,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_2336,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1854])).

cnf(c_2337,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2336])).

cnf(c_5,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_178,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_7])).

cnf(c_179,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_1227,plain,
    ( v1_tsep_1(X0_49,X1_49)
    | ~ v3_pre_topc(u1_struct_0(X0_49),X1_49)
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v2_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_2165,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_1248,plain,
    ( m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2142,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2139,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2128,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1242,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1863,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_14,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1244,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1909,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1863,c_1244])).

cnf(c_2078,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1909])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1245,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1861,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_1920,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1861,c_1244])).

cnf(c_2076,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1920])).

cnf(c_6,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_171,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_7])).

cnf(c_172,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_19,negated_conjecture,
    ( v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_462,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_19])).

cnf(c_463,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3321,c_3281,c_3071,c_2995,c_2994,c_2901,c_2558,c_2419,c_2358,c_2357,c_2337,c_2165,c_2142,c_2139,c_2128,c_2078,c_2076,c_1244,c_463,c_12,c_13,c_15,c_16,c_17,c_20,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.16/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.16/1.01  
% 1.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.16/1.01  
% 1.16/1.01  ------  iProver source info
% 1.16/1.01  
% 1.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.16/1.01  git: non_committed_changes: false
% 1.16/1.01  git: last_make_outside_of_git: false
% 1.16/1.01  
% 1.16/1.01  ------ 
% 1.16/1.01  
% 1.16/1.01  ------ Input Options
% 1.16/1.01  
% 1.16/1.01  --out_options                           all
% 1.16/1.01  --tptp_safe_out                         true
% 1.16/1.01  --problem_path                          ""
% 1.16/1.01  --include_path                          ""
% 1.16/1.01  --clausifier                            res/vclausify_rel
% 1.16/1.01  --clausifier_options                    --mode clausify
% 1.16/1.01  --stdin                                 false
% 1.16/1.01  --stats_out                             all
% 1.16/1.01  
% 1.16/1.01  ------ General Options
% 1.16/1.01  
% 1.16/1.01  --fof                                   false
% 1.16/1.01  --time_out_real                         305.
% 1.16/1.01  --time_out_virtual                      -1.
% 1.16/1.01  --symbol_type_check                     false
% 1.16/1.01  --clausify_out                          false
% 1.16/1.01  --sig_cnt_out                           false
% 1.16/1.01  --trig_cnt_out                          false
% 1.16/1.01  --trig_cnt_out_tolerance                1.
% 1.16/1.01  --trig_cnt_out_sk_spl                   false
% 1.16/1.01  --abstr_cl_out                          false
% 1.16/1.01  
% 1.16/1.01  ------ Global Options
% 1.16/1.01  
% 1.16/1.01  --schedule                              default
% 1.16/1.01  --add_important_lit                     false
% 1.16/1.01  --prop_solver_per_cl                    1000
% 1.16/1.01  --min_unsat_core                        false
% 1.16/1.01  --soft_assumptions                      false
% 1.16/1.01  --soft_lemma_size                       3
% 1.16/1.01  --prop_impl_unit_size                   0
% 1.16/1.01  --prop_impl_unit                        []
% 1.16/1.01  --share_sel_clauses                     true
% 1.16/1.01  --reset_solvers                         false
% 1.16/1.01  --bc_imp_inh                            [conj_cone]
% 1.16/1.01  --conj_cone_tolerance                   3.
% 1.16/1.01  --extra_neg_conj                        none
% 1.16/1.01  --large_theory_mode                     true
% 1.16/1.01  --prolific_symb_bound                   200
% 1.16/1.01  --lt_threshold                          2000
% 1.16/1.01  --clause_weak_htbl                      true
% 1.16/1.01  --gc_record_bc_elim                     false
% 1.16/1.01  
% 1.16/1.01  ------ Preprocessing Options
% 1.16/1.01  
% 1.16/1.01  --preprocessing_flag                    true
% 1.16/1.01  --time_out_prep_mult                    0.1
% 1.16/1.01  --splitting_mode                        input
% 1.16/1.01  --splitting_grd                         true
% 1.16/1.01  --splitting_cvd                         false
% 1.16/1.01  --splitting_cvd_svl                     false
% 1.16/1.01  --splitting_nvd                         32
% 1.16/1.01  --sub_typing                            true
% 1.16/1.01  --prep_gs_sim                           true
% 1.16/1.01  --prep_unflatten                        true
% 1.16/1.01  --prep_res_sim                          true
% 1.16/1.01  --prep_upred                            true
% 1.16/1.01  --prep_sem_filter                       exhaustive
% 1.16/1.01  --prep_sem_filter_out                   false
% 1.16/1.01  --pred_elim                             true
% 1.16/1.01  --res_sim_input                         true
% 1.16/1.01  --eq_ax_congr_red                       true
% 1.16/1.01  --pure_diseq_elim                       true
% 1.16/1.01  --brand_transform                       false
% 1.16/1.01  --non_eq_to_eq                          false
% 1.16/1.01  --prep_def_merge                        true
% 1.16/1.01  --prep_def_merge_prop_impl              false
% 1.16/1.01  --prep_def_merge_mbd                    true
% 1.16/1.01  --prep_def_merge_tr_red                 false
% 1.16/1.01  --prep_def_merge_tr_cl                  false
% 1.16/1.01  --smt_preprocessing                     true
% 1.16/1.01  --smt_ac_axioms                         fast
% 1.16/1.01  --preprocessed_out                      false
% 1.16/1.01  --preprocessed_stats                    false
% 1.16/1.01  
% 1.16/1.01  ------ Abstraction refinement Options
% 1.16/1.01  
% 1.16/1.01  --abstr_ref                             []
% 1.16/1.01  --abstr_ref_prep                        false
% 1.16/1.01  --abstr_ref_until_sat                   false
% 1.16/1.01  --abstr_ref_sig_restrict                funpre
% 1.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.16/1.01  --abstr_ref_under                       []
% 1.16/1.01  
% 1.16/1.01  ------ SAT Options
% 1.16/1.01  
% 1.16/1.01  --sat_mode                              false
% 1.16/1.01  --sat_fm_restart_options                ""
% 1.16/1.01  --sat_gr_def                            false
% 1.16/1.01  --sat_epr_types                         true
% 1.16/1.01  --sat_non_cyclic_types                  false
% 1.16/1.01  --sat_finite_models                     false
% 1.16/1.01  --sat_fm_lemmas                         false
% 1.16/1.01  --sat_fm_prep                           false
% 1.16/1.01  --sat_fm_uc_incr                        true
% 1.16/1.01  --sat_out_model                         small
% 1.16/1.01  --sat_out_clauses                       false
% 1.16/1.01  
% 1.16/1.01  ------ QBF Options
% 1.16/1.01  
% 1.16/1.01  --qbf_mode                              false
% 1.16/1.01  --qbf_elim_univ                         false
% 1.16/1.01  --qbf_dom_inst                          none
% 1.16/1.01  --qbf_dom_pre_inst                      false
% 1.16/1.01  --qbf_sk_in                             false
% 1.16/1.01  --qbf_pred_elim                         true
% 1.16/1.01  --qbf_split                             512
% 1.16/1.01  
% 1.16/1.01  ------ BMC1 Options
% 1.16/1.01  
% 1.16/1.01  --bmc1_incremental                      false
% 1.16/1.01  --bmc1_axioms                           reachable_all
% 1.16/1.01  --bmc1_min_bound                        0
% 1.16/1.01  --bmc1_max_bound                        -1
% 1.16/1.01  --bmc1_max_bound_default                -1
% 1.16/1.01  --bmc1_symbol_reachability              true
% 1.16/1.01  --bmc1_property_lemmas                  false
% 1.16/1.01  --bmc1_k_induction                      false
% 1.16/1.01  --bmc1_non_equiv_states                 false
% 1.16/1.01  --bmc1_deadlock                         false
% 1.16/1.01  --bmc1_ucm                              false
% 1.16/1.01  --bmc1_add_unsat_core                   none
% 1.16/1.01  --bmc1_unsat_core_children              false
% 1.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.16/1.01  --bmc1_out_stat                         full
% 1.16/1.01  --bmc1_ground_init                      false
% 1.16/1.01  --bmc1_pre_inst_next_state              false
% 1.16/1.01  --bmc1_pre_inst_state                   false
% 1.16/1.01  --bmc1_pre_inst_reach_state             false
% 1.16/1.01  --bmc1_out_unsat_core                   false
% 1.16/1.01  --bmc1_aig_witness_out                  false
% 1.16/1.01  --bmc1_verbose                          false
% 1.16/1.01  --bmc1_dump_clauses_tptp                false
% 1.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.16/1.01  --bmc1_dump_file                        -
% 1.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.16/1.01  --bmc1_ucm_extend_mode                  1
% 1.16/1.01  --bmc1_ucm_init_mode                    2
% 1.16/1.01  --bmc1_ucm_cone_mode                    none
% 1.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.16/1.01  --bmc1_ucm_relax_model                  4
% 1.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.16/1.01  --bmc1_ucm_layered_model                none
% 1.16/1.01  --bmc1_ucm_max_lemma_size               10
% 1.16/1.01  
% 1.16/1.01  ------ AIG Options
% 1.16/1.01  
% 1.16/1.01  --aig_mode                              false
% 1.16/1.01  
% 1.16/1.01  ------ Instantiation Options
% 1.16/1.01  
% 1.16/1.01  --instantiation_flag                    true
% 1.16/1.01  --inst_sos_flag                         false
% 1.16/1.01  --inst_sos_phase                        true
% 1.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.16/1.01  --inst_lit_sel_side                     num_symb
% 1.16/1.01  --inst_solver_per_active                1400
% 1.16/1.01  --inst_solver_calls_frac                1.
% 1.16/1.01  --inst_passive_queue_type               priority_queues
% 1.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.16/1.01  --inst_passive_queues_freq              [25;2]
% 1.16/1.01  --inst_dismatching                      true
% 1.16/1.01  --inst_eager_unprocessed_to_passive     true
% 1.16/1.01  --inst_prop_sim_given                   true
% 1.16/1.01  --inst_prop_sim_new                     false
% 1.16/1.01  --inst_subs_new                         false
% 1.16/1.01  --inst_eq_res_simp                      false
% 1.16/1.01  --inst_subs_given                       false
% 1.16/1.01  --inst_orphan_elimination               true
% 1.16/1.01  --inst_learning_loop_flag               true
% 1.16/1.01  --inst_learning_start                   3000
% 1.16/1.01  --inst_learning_factor                  2
% 1.16/1.01  --inst_start_prop_sim_after_learn       3
% 1.16/1.01  --inst_sel_renew                        solver
% 1.16/1.01  --inst_lit_activity_flag                true
% 1.16/1.01  --inst_restr_to_given                   false
% 1.16/1.01  --inst_activity_threshold               500
% 1.16/1.01  --inst_out_proof                        true
% 1.16/1.01  
% 1.16/1.01  ------ Resolution Options
% 1.16/1.01  
% 1.16/1.01  --resolution_flag                       true
% 1.16/1.01  --res_lit_sel                           adaptive
% 1.16/1.01  --res_lit_sel_side                      none
% 1.16/1.01  --res_ordering                          kbo
% 1.16/1.01  --res_to_prop_solver                    active
% 1.16/1.01  --res_prop_simpl_new                    false
% 1.16/1.01  --res_prop_simpl_given                  true
% 1.16/1.01  --res_passive_queue_type                priority_queues
% 1.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.16/1.01  --res_passive_queues_freq               [15;5]
% 1.16/1.01  --res_forward_subs                      full
% 1.16/1.01  --res_backward_subs                     full
% 1.16/1.01  --res_forward_subs_resolution           true
% 1.16/1.01  --res_backward_subs_resolution          true
% 1.16/1.01  --res_orphan_elimination                true
% 1.16/1.01  --res_time_limit                        2.
% 1.16/1.01  --res_out_proof                         true
% 1.16/1.01  
% 1.16/1.01  ------ Superposition Options
% 1.16/1.01  
% 1.16/1.01  --superposition_flag                    true
% 1.16/1.01  --sup_passive_queue_type                priority_queues
% 1.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.16/1.01  --demod_completeness_check              fast
% 1.16/1.01  --demod_use_ground                      true
% 1.16/1.01  --sup_to_prop_solver                    passive
% 1.16/1.01  --sup_prop_simpl_new                    true
% 1.16/1.01  --sup_prop_simpl_given                  true
% 1.16/1.01  --sup_fun_splitting                     false
% 1.16/1.01  --sup_smt_interval                      50000
% 1.16/1.01  
% 1.16/1.01  ------ Superposition Simplification Setup
% 1.16/1.01  
% 1.16/1.01  --sup_indices_passive                   []
% 1.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_full_bw                           [BwDemod]
% 1.16/1.01  --sup_immed_triv                        [TrivRules]
% 1.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_immed_bw_main                     []
% 1.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/1.01  
% 1.16/1.01  ------ Combination Options
% 1.16/1.01  
% 1.16/1.01  --comb_res_mult                         3
% 1.16/1.01  --comb_sup_mult                         2
% 1.16/1.01  --comb_inst_mult                        10
% 1.16/1.01  
% 1.16/1.01  ------ Debug Options
% 1.16/1.01  
% 1.16/1.01  --dbg_backtrace                         false
% 1.16/1.01  --dbg_dump_prop_clauses                 false
% 1.16/1.01  --dbg_dump_prop_clauses_file            -
% 1.16/1.01  --dbg_out_stat                          false
% 1.16/1.01  ------ Parsing...
% 1.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.16/1.01  
% 1.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.16/1.01  
% 1.16/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.16/1.01  
% 1.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.16/1.01  ------ Proving...
% 1.16/1.01  ------ Problem Properties 
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  clauses                                 28
% 1.16/1.01  conjectures                             18
% 1.16/1.01  EPR                                     16
% 1.16/1.01  Horn                                    25
% 1.16/1.01  unary                                   16
% 1.16/1.01  binary                                  2
% 1.16/1.01  lits                                    90
% 1.16/1.01  lits eq                                 5
% 1.16/1.01  fd_pure                                 0
% 1.16/1.01  fd_pseudo                               0
% 1.16/1.01  fd_cond                                 0
% 1.16/1.01  fd_pseudo_cond                          0
% 1.16/1.01  AC symbols                              0
% 1.16/1.01  
% 1.16/1.01  ------ Schedule dynamic 5 is on 
% 1.16/1.01  
% 1.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  ------ 
% 1.16/1.01  Current options:
% 1.16/1.01  ------ 
% 1.16/1.01  
% 1.16/1.01  ------ Input Options
% 1.16/1.01  
% 1.16/1.01  --out_options                           all
% 1.16/1.01  --tptp_safe_out                         true
% 1.16/1.01  --problem_path                          ""
% 1.16/1.01  --include_path                          ""
% 1.16/1.01  --clausifier                            res/vclausify_rel
% 1.16/1.01  --clausifier_options                    --mode clausify
% 1.16/1.01  --stdin                                 false
% 1.16/1.01  --stats_out                             all
% 1.16/1.01  
% 1.16/1.01  ------ General Options
% 1.16/1.01  
% 1.16/1.01  --fof                                   false
% 1.16/1.01  --time_out_real                         305.
% 1.16/1.01  --time_out_virtual                      -1.
% 1.16/1.01  --symbol_type_check                     false
% 1.16/1.01  --clausify_out                          false
% 1.16/1.01  --sig_cnt_out                           false
% 1.16/1.01  --trig_cnt_out                          false
% 1.16/1.01  --trig_cnt_out_tolerance                1.
% 1.16/1.01  --trig_cnt_out_sk_spl                   false
% 1.16/1.01  --abstr_cl_out                          false
% 1.16/1.01  
% 1.16/1.01  ------ Global Options
% 1.16/1.01  
% 1.16/1.01  --schedule                              default
% 1.16/1.01  --add_important_lit                     false
% 1.16/1.01  --prop_solver_per_cl                    1000
% 1.16/1.01  --min_unsat_core                        false
% 1.16/1.01  --soft_assumptions                      false
% 1.16/1.01  --soft_lemma_size                       3
% 1.16/1.01  --prop_impl_unit_size                   0
% 1.16/1.01  --prop_impl_unit                        []
% 1.16/1.01  --share_sel_clauses                     true
% 1.16/1.01  --reset_solvers                         false
% 1.16/1.01  --bc_imp_inh                            [conj_cone]
% 1.16/1.01  --conj_cone_tolerance                   3.
% 1.16/1.01  --extra_neg_conj                        none
% 1.16/1.01  --large_theory_mode                     true
% 1.16/1.01  --prolific_symb_bound                   200
% 1.16/1.01  --lt_threshold                          2000
% 1.16/1.01  --clause_weak_htbl                      true
% 1.16/1.01  --gc_record_bc_elim                     false
% 1.16/1.01  
% 1.16/1.01  ------ Preprocessing Options
% 1.16/1.01  
% 1.16/1.01  --preprocessing_flag                    true
% 1.16/1.01  --time_out_prep_mult                    0.1
% 1.16/1.01  --splitting_mode                        input
% 1.16/1.01  --splitting_grd                         true
% 1.16/1.01  --splitting_cvd                         false
% 1.16/1.01  --splitting_cvd_svl                     false
% 1.16/1.01  --splitting_nvd                         32
% 1.16/1.01  --sub_typing                            true
% 1.16/1.01  --prep_gs_sim                           true
% 1.16/1.01  --prep_unflatten                        true
% 1.16/1.01  --prep_res_sim                          true
% 1.16/1.01  --prep_upred                            true
% 1.16/1.01  --prep_sem_filter                       exhaustive
% 1.16/1.01  --prep_sem_filter_out                   false
% 1.16/1.01  --pred_elim                             true
% 1.16/1.01  --res_sim_input                         true
% 1.16/1.01  --eq_ax_congr_red                       true
% 1.16/1.01  --pure_diseq_elim                       true
% 1.16/1.01  --brand_transform                       false
% 1.16/1.01  --non_eq_to_eq                          false
% 1.16/1.01  --prep_def_merge                        true
% 1.16/1.01  --prep_def_merge_prop_impl              false
% 1.16/1.01  --prep_def_merge_mbd                    true
% 1.16/1.01  --prep_def_merge_tr_red                 false
% 1.16/1.01  --prep_def_merge_tr_cl                  false
% 1.16/1.01  --smt_preprocessing                     true
% 1.16/1.01  --smt_ac_axioms                         fast
% 1.16/1.01  --preprocessed_out                      false
% 1.16/1.01  --preprocessed_stats                    false
% 1.16/1.01  
% 1.16/1.01  ------ Abstraction refinement Options
% 1.16/1.01  
% 1.16/1.01  --abstr_ref                             []
% 1.16/1.01  --abstr_ref_prep                        false
% 1.16/1.01  --abstr_ref_until_sat                   false
% 1.16/1.01  --abstr_ref_sig_restrict                funpre
% 1.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.16/1.01  --abstr_ref_under                       []
% 1.16/1.01  
% 1.16/1.01  ------ SAT Options
% 1.16/1.01  
% 1.16/1.01  --sat_mode                              false
% 1.16/1.01  --sat_fm_restart_options                ""
% 1.16/1.01  --sat_gr_def                            false
% 1.16/1.01  --sat_epr_types                         true
% 1.16/1.01  --sat_non_cyclic_types                  false
% 1.16/1.01  --sat_finite_models                     false
% 1.16/1.01  --sat_fm_lemmas                         false
% 1.16/1.01  --sat_fm_prep                           false
% 1.16/1.01  --sat_fm_uc_incr                        true
% 1.16/1.01  --sat_out_model                         small
% 1.16/1.01  --sat_out_clauses                       false
% 1.16/1.01  
% 1.16/1.01  ------ QBF Options
% 1.16/1.01  
% 1.16/1.01  --qbf_mode                              false
% 1.16/1.01  --qbf_elim_univ                         false
% 1.16/1.01  --qbf_dom_inst                          none
% 1.16/1.01  --qbf_dom_pre_inst                      false
% 1.16/1.01  --qbf_sk_in                             false
% 1.16/1.01  --qbf_pred_elim                         true
% 1.16/1.01  --qbf_split                             512
% 1.16/1.01  
% 1.16/1.01  ------ BMC1 Options
% 1.16/1.01  
% 1.16/1.01  --bmc1_incremental                      false
% 1.16/1.01  --bmc1_axioms                           reachable_all
% 1.16/1.01  --bmc1_min_bound                        0
% 1.16/1.01  --bmc1_max_bound                        -1
% 1.16/1.01  --bmc1_max_bound_default                -1
% 1.16/1.01  --bmc1_symbol_reachability              true
% 1.16/1.01  --bmc1_property_lemmas                  false
% 1.16/1.01  --bmc1_k_induction                      false
% 1.16/1.01  --bmc1_non_equiv_states                 false
% 1.16/1.01  --bmc1_deadlock                         false
% 1.16/1.01  --bmc1_ucm                              false
% 1.16/1.01  --bmc1_add_unsat_core                   none
% 1.16/1.01  --bmc1_unsat_core_children              false
% 1.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.16/1.01  --bmc1_out_stat                         full
% 1.16/1.01  --bmc1_ground_init                      false
% 1.16/1.01  --bmc1_pre_inst_next_state              false
% 1.16/1.01  --bmc1_pre_inst_state                   false
% 1.16/1.01  --bmc1_pre_inst_reach_state             false
% 1.16/1.01  --bmc1_out_unsat_core                   false
% 1.16/1.01  --bmc1_aig_witness_out                  false
% 1.16/1.01  --bmc1_verbose                          false
% 1.16/1.01  --bmc1_dump_clauses_tptp                false
% 1.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.16/1.01  --bmc1_dump_file                        -
% 1.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.16/1.01  --bmc1_ucm_extend_mode                  1
% 1.16/1.01  --bmc1_ucm_init_mode                    2
% 1.16/1.01  --bmc1_ucm_cone_mode                    none
% 1.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.16/1.01  --bmc1_ucm_relax_model                  4
% 1.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.16/1.01  --bmc1_ucm_layered_model                none
% 1.16/1.01  --bmc1_ucm_max_lemma_size               10
% 1.16/1.01  
% 1.16/1.01  ------ AIG Options
% 1.16/1.01  
% 1.16/1.01  --aig_mode                              false
% 1.16/1.01  
% 1.16/1.01  ------ Instantiation Options
% 1.16/1.01  
% 1.16/1.01  --instantiation_flag                    true
% 1.16/1.01  --inst_sos_flag                         false
% 1.16/1.01  --inst_sos_phase                        true
% 1.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.16/1.01  --inst_lit_sel_side                     none
% 1.16/1.01  --inst_solver_per_active                1400
% 1.16/1.01  --inst_solver_calls_frac                1.
% 1.16/1.01  --inst_passive_queue_type               priority_queues
% 1.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.16/1.01  --inst_passive_queues_freq              [25;2]
% 1.16/1.01  --inst_dismatching                      true
% 1.16/1.01  --inst_eager_unprocessed_to_passive     true
% 1.16/1.01  --inst_prop_sim_given                   true
% 1.16/1.01  --inst_prop_sim_new                     false
% 1.16/1.01  --inst_subs_new                         false
% 1.16/1.01  --inst_eq_res_simp                      false
% 1.16/1.01  --inst_subs_given                       false
% 1.16/1.01  --inst_orphan_elimination               true
% 1.16/1.01  --inst_learning_loop_flag               true
% 1.16/1.01  --inst_learning_start                   3000
% 1.16/1.01  --inst_learning_factor                  2
% 1.16/1.01  --inst_start_prop_sim_after_learn       3
% 1.16/1.01  --inst_sel_renew                        solver
% 1.16/1.01  --inst_lit_activity_flag                true
% 1.16/1.01  --inst_restr_to_given                   false
% 1.16/1.01  --inst_activity_threshold               500
% 1.16/1.01  --inst_out_proof                        true
% 1.16/1.01  
% 1.16/1.01  ------ Resolution Options
% 1.16/1.01  
% 1.16/1.01  --resolution_flag                       false
% 1.16/1.01  --res_lit_sel                           adaptive
% 1.16/1.01  --res_lit_sel_side                      none
% 1.16/1.01  --res_ordering                          kbo
% 1.16/1.01  --res_to_prop_solver                    active
% 1.16/1.01  --res_prop_simpl_new                    false
% 1.16/1.01  --res_prop_simpl_given                  true
% 1.16/1.01  --res_passive_queue_type                priority_queues
% 1.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.16/1.01  --res_passive_queues_freq               [15;5]
% 1.16/1.01  --res_forward_subs                      full
% 1.16/1.01  --res_backward_subs                     full
% 1.16/1.01  --res_forward_subs_resolution           true
% 1.16/1.01  --res_backward_subs_resolution          true
% 1.16/1.01  --res_orphan_elimination                true
% 1.16/1.01  --res_time_limit                        2.
% 1.16/1.01  --res_out_proof                         true
% 1.16/1.01  
% 1.16/1.01  ------ Superposition Options
% 1.16/1.01  
% 1.16/1.01  --superposition_flag                    true
% 1.16/1.01  --sup_passive_queue_type                priority_queues
% 1.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.16/1.01  --demod_completeness_check              fast
% 1.16/1.01  --demod_use_ground                      true
% 1.16/1.01  --sup_to_prop_solver                    passive
% 1.16/1.01  --sup_prop_simpl_new                    true
% 1.16/1.01  --sup_prop_simpl_given                  true
% 1.16/1.01  --sup_fun_splitting                     false
% 1.16/1.01  --sup_smt_interval                      50000
% 1.16/1.01  
% 1.16/1.01  ------ Superposition Simplification Setup
% 1.16/1.01  
% 1.16/1.01  --sup_indices_passive                   []
% 1.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_full_bw                           [BwDemod]
% 1.16/1.01  --sup_immed_triv                        [TrivRules]
% 1.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_immed_bw_main                     []
% 1.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/1.01  
% 1.16/1.01  ------ Combination Options
% 1.16/1.01  
% 1.16/1.01  --comb_res_mult                         3
% 1.16/1.01  --comb_sup_mult                         2
% 1.16/1.01  --comb_inst_mult                        10
% 1.16/1.01  
% 1.16/1.01  ------ Debug Options
% 1.16/1.01  
% 1.16/1.01  --dbg_backtrace                         false
% 1.16/1.01  --dbg_dump_prop_clauses                 false
% 1.16/1.01  --dbg_dump_prop_clauses_file            -
% 1.16/1.01  --dbg_out_stat                          false
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  ------ Proving...
% 1.16/1.01  
% 1.16/1.01  
% 1.16/1.01  % SZS status Theorem for theBenchmark.p
% 1.16/1.01  
% 1.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.16/1.01  
% 1.16/1.01  fof(f9,axiom,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f25,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f9])).
% 1.16/1.01  
% 1.16/1.01  fof(f26,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.16/1.01    inference(flattening,[],[f25])).
% 1.16/1.01  
% 1.16/1.01  fof(f31,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.16/1.01    inference(nnf_transformation,[],[f26])).
% 1.16/1.01  
% 1.16/1.01  fof(f52,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f31])).
% 1.16/1.01  
% 1.16/1.01  fof(f81,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f52])).
% 1.16/1.01  
% 1.16/1.01  fof(f8,axiom,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f23,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f8])).
% 1.16/1.01  
% 1.16/1.01  fof(f24,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.16/1.01    inference(flattening,[],[f23])).
% 1.16/1.01  
% 1.16/1.01  fof(f51,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f24])).
% 1.16/1.01  
% 1.16/1.01  fof(f79,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f51])).
% 1.16/1.01  
% 1.16/1.01  fof(f10,conjecture,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f11,negated_conjecture,(
% 1.16/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.16/1.01    inference(negated_conjecture,[],[f10])).
% 1.16/1.01  
% 1.16/1.01  fof(f27,plain,(
% 1.16/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f11])).
% 1.16/1.01  
% 1.16/1.01  fof(f28,plain,(
% 1.16/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.16/1.01    inference(flattening,[],[f27])).
% 1.16/1.01  
% 1.16/1.01  fof(f32,plain,(
% 1.16/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.16/1.01    inference(nnf_transformation,[],[f28])).
% 1.16/1.01  
% 1.16/1.01  fof(f33,plain,(
% 1.16/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.16/1.01    inference(flattening,[],[f32])).
% 1.16/1.01  
% 1.16/1.01  fof(f40,plain,(
% 1.16/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | r1_tmap_1(X3,X0,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f39,plain,(
% 1.16/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f38,plain,(
% 1.16/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X0,sK4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | r1_tmap_1(X3,X0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f37,plain,(
% 1.16/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | r1_tmap_1(sK3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f36,plain,(
% 1.16/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,X1) & v1_tsep_1(sK2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f35,plain,(
% 1.16/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f34,plain,(
% 1.16/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.16/1.01    introduced(choice_axiom,[])).
% 1.16/1.01  
% 1.16/1.01  fof(f41,plain,(
% 1.16/1.01    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f33,f40,f39,f38,f37,f36,f35,f34])).
% 1.16/1.01  
% 1.16/1.01  fof(f65,plain,(
% 1.16/1.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f64,plain,(
% 1.16/1.01    v1_funct_1(sK4)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f7,axiom,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f21,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f7])).
% 1.16/1.01  
% 1.16/1.01  fof(f22,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.16/1.01    inference(flattening,[],[f21])).
% 1.16/1.01  
% 1.16/1.01  fof(f50,plain,(
% 1.16/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f22])).
% 1.16/1.01  
% 1.16/1.01  fof(f53,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f31])).
% 1.16/1.01  
% 1.16/1.01  fof(f80,plain,(
% 1.16/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f53])).
% 1.16/1.01  
% 1.16/1.01  fof(f2,axiom,(
% 1.16/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f14,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.16/1.01    inference(ennf_transformation,[],[f2])).
% 1.16/1.01  
% 1.16/1.01  fof(f43,plain,(
% 1.16/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f14])).
% 1.16/1.01  
% 1.16/1.01  fof(f4,axiom,(
% 1.16/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f16,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.16/1.01    inference(ennf_transformation,[],[f4])).
% 1.16/1.01  
% 1.16/1.01  fof(f17,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.16/1.01    inference(flattening,[],[f16])).
% 1.16/1.01  
% 1.16/1.01  fof(f45,plain,(
% 1.16/1.01    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f17])).
% 1.16/1.01  
% 1.16/1.01  fof(f75,plain,(
% 1.16/1.01    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f45])).
% 1.16/1.01  
% 1.16/1.01  fof(f63,plain,(
% 1.16/1.01    m1_pre_topc(sK3,sK1)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f1,axiom,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f12,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f1])).
% 1.16/1.01  
% 1.16/1.01  fof(f13,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.16/1.01    inference(flattening,[],[f12])).
% 1.16/1.01  
% 1.16/1.01  fof(f42,plain,(
% 1.16/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f13])).
% 1.16/1.01  
% 1.16/1.01  fof(f5,axiom,(
% 1.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f18,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.16/1.01    inference(ennf_transformation,[],[f5])).
% 1.16/1.01  
% 1.16/1.01  fof(f19,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.16/1.01    inference(flattening,[],[f18])).
% 1.16/1.01  
% 1.16/1.01  fof(f29,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.16/1.01    inference(nnf_transformation,[],[f19])).
% 1.16/1.01  
% 1.16/1.01  fof(f30,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.16/1.01    inference(flattening,[],[f29])).
% 1.16/1.01  
% 1.16/1.01  fof(f47,plain,(
% 1.16/1.01    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f30])).
% 1.16/1.01  
% 1.16/1.01  fof(f77,plain,(
% 1.16/1.01    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f47])).
% 1.16/1.01  
% 1.16/1.01  fof(f6,axiom,(
% 1.16/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.01  
% 1.16/1.01  fof(f20,plain,(
% 1.16/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.16/1.01    inference(ennf_transformation,[],[f6])).
% 1.16/1.01  
% 1.16/1.01  fof(f49,plain,(
% 1.16/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f20])).
% 1.16/1.01  
% 1.16/1.01  fof(f70,plain,(
% 1.16/1.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f72,plain,(
% 1.16/1.01    sK5 = sK6),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f73,plain,(
% 1.16/1.01    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f46,plain,(
% 1.16/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(cnf_transformation,[],[f30])).
% 1.16/1.01  
% 1.16/1.01  fof(f78,plain,(
% 1.16/1.01    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.16/1.01    inference(equality_resolution,[],[f46])).
% 1.16/1.01  
% 1.16/1.01  fof(f67,plain,(
% 1.16/1.01    v1_tsep_1(sK2,sK1)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f74,plain,(
% 1.16/1.01    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f71,plain,(
% 1.16/1.01    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f69,plain,(
% 1.16/1.01    m1_pre_topc(sK2,sK3)),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f66,plain,(
% 1.16/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.16/1.01    inference(cnf_transformation,[],[f41])).
% 1.16/1.01  
% 1.16/1.01  fof(f62,plain,(
% 1.16/1.02    ~v2_struct_0(sK3)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f61,plain,(
% 1.16/1.02    m1_pre_topc(sK2,sK1)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f60,plain,(
% 1.16/1.02    ~v2_struct_0(sK2)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f59,plain,(
% 1.16/1.02    l1_pre_topc(sK1)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f58,plain,(
% 1.16/1.02    v2_pre_topc(sK1)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f57,plain,(
% 1.16/1.02    ~v2_struct_0(sK1)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f56,plain,(
% 1.16/1.02    l1_pre_topc(sK0)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f55,plain,(
% 1.16/1.02    v2_pre_topc(sK0)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  fof(f54,plain,(
% 1.16/1.02    ~v2_struct_0(sK0)),
% 1.16/1.02    inference(cnf_transformation,[],[f41])).
% 1.16/1.02  
% 1.16/1.02  cnf(c_11,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.16/1.02      | ~ v1_tsep_1(X4,X0)
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f81]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_9,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f79]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_162,plain,
% 1.16/1.02      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.16/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(global_propositional_subsumption,
% 1.16/1.02                [status(thm)],
% 1.16/1.02                [c_11,c_9]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_163,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5) ),
% 1.16/1.02      inference(renaming,[status(thm)],[c_162]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_21,negated_conjecture,
% 1.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 1.16/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_531,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.16/1.02      | sK4 != X2 ),
% 1.16/1.02      inference(resolution_lifted,[status(thm)],[c_163,c_21]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_532,plain,
% 1.16/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | ~ v1_funct_1(sK4)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(unflattening,[status(thm)],[c_531]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_22,negated_conjecture,
% 1.16/1.02      ( v1_funct_1(sK4) ),
% 1.16/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_536,plain,
% 1.16/1.02      ( v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(global_propositional_subsumption,
% 1.16/1.02                [status(thm)],
% 1.16/1.02                [c_532,c_22]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_537,plain,
% 1.16/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(renaming,[status(thm)],[c_536]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_8,plain,
% 1.16/1.02      ( ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ m1_pre_topc(X2,X0)
% 1.16/1.02      | m1_pre_topc(X2,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_578,plain,
% 1.16/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_537,c_8]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1226,plain,
% 1.16/1.02      ( r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,X3_49,X0_49,sK4),X0_50)
% 1.16/1.02      | ~ r1_tmap_1(X3_49,X1_49,sK4,X0_50)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X3_49))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
% 1.16/1.02      | ~ m1_pre_topc(X3_49,X2_49)
% 1.16/1.02      | ~ m1_pre_topc(X0_49,X3_49)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(X2_49)
% 1.16/1.02      | v2_struct_0(X3_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X2_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X2_49)
% 1.16/1.02      | u1_struct_0(X3_49) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1_49) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_578]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2130,plain,
% 1.16/1.02      ( r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,sK3,X0_49,sK4),X0_50)
% 1.16/1.02      | ~ r1_tmap_1(sK3,X1_49,sK4,X0_50)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_49))))
% 1.16/1.02      | ~ m1_pre_topc(X0_49,sK3)
% 1.16/1.02      | ~ m1_pre_topc(sK3,X2_49)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(X2_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X2_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X2_49)
% 1.16/1.02      | u1_struct_0(X1_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1226]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2463,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,X0_49,sK4,X0_50)
% 1.16/1.02      | r1_tmap_1(sK2,X0_49,k3_tmap_1(X1_49,X0_49,sK3,sK2,sK4),X0_50)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,X1_49)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2130]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2850,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,X0_49,sK4,X0_50)
% 1.16/1.02      | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),X0_50)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2463]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3319,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,X0_49,sK4,sK6)
% 1.16/1.02      | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK6)
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2850]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3321,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK0)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK0)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_3319]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_10,plain,
% 1.16/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.16/1.02      | ~ v1_tsep_1(X4,X0)
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f80]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_597,plain,
% 1.16/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 1.16/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.16/1.02      | ~ v1_tsep_1(X4,X0)
% 1.16/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_pre_topc(X0,X5)
% 1.16/1.02      | ~ m1_pre_topc(X4,X0)
% 1.16/1.02      | ~ m1_pre_topc(X4,X5)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X5)
% 1.16/1.02      | v2_struct_0(X4)
% 1.16/1.02      | ~ v1_funct_1(X2)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X5)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X5)
% 1.16/1.02      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.16/1.02      | sK4 != X2 ),
% 1.16/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_598,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ v1_tsep_1(X0,X3)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | ~ v1_funct_1(sK4)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(unflattening,[status(thm)],[c_597]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_602,plain,
% 1.16/1.02      ( v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ v1_tsep_1(X0,X3)
% 1.16/1.02      | r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(global_propositional_subsumption,
% 1.16/1.02                [status(thm)],
% 1.16/1.02                [c_598,c_22]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_603,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ v1_tsep_1(X0,X3)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | ~ m1_pre_topc(X0,X2)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(renaming,[status(thm)],[c_602]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_646,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.16/1.02      | r1_tmap_1(X3,X1,sK4,X4)
% 1.16/1.02      | ~ v1_tsep_1(X0,X3)
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.16/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.16/1.02      | ~ m1_pre_topc(X3,X2)
% 1.16/1.02      | ~ m1_pre_topc(X0,X3)
% 1.16/1.02      | v2_struct_0(X1)
% 1.16/1.02      | v2_struct_0(X0)
% 1.16/1.02      | v2_struct_0(X2)
% 1.16/1.02      | v2_struct_0(X3)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ l1_pre_topc(X2)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X2)
% 1.16/1.02      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_603,c_8]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1225,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,X3_49,X0_49,sK4),X0_50)
% 1.16/1.02      | r1_tmap_1(X3_49,X1_49,sK4,X0_50)
% 1.16/1.02      | ~ v1_tsep_1(X0_49,X3_49)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X3_49))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
% 1.16/1.02      | ~ m1_pre_topc(X3_49,X2_49)
% 1.16/1.02      | ~ m1_pre_topc(X0_49,X3_49)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(X2_49)
% 1.16/1.02      | v2_struct_0(X3_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X2_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X2_49)
% 1.16/1.02      | u1_struct_0(X3_49) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(X1_49) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_646]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2129,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0_49,X1_49,k3_tmap_1(X2_49,X1_49,sK3,X0_49,sK4),X0_50)
% 1.16/1.02      | r1_tmap_1(sK3,X1_49,sK4,X0_50)
% 1.16/1.02      | ~ v1_tsep_1(X0_49,sK3)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_49))))
% 1.16/1.02      | ~ m1_pre_topc(X0_49,sK3)
% 1.16/1.02      | ~ m1_pre_topc(sK3,X2_49)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(X2_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X2_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X2_49)
% 1.16/1.02      | u1_struct_0(X1_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2621,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,X0_49,sK4,X0_50)
% 1.16/1.02      | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(X1_49,X0_49,sK3,sK2,sK4),X0_50)
% 1.16/1.02      | ~ v1_tsep_1(sK2,sK3)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,X1_49)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X1_49)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2129]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2920,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,X0_49,sK4,X0_50)
% 1.16/1.02      | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),X0_50)
% 1.16/1.02      | ~ v1_tsep_1(sK2,sK3)
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2621]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3279,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,X0_49,sK4,sK5)
% 1.16/1.02      | ~ r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK5)
% 1.16/1.02      | ~ v1_tsep_1(sK2,sK3)
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2920]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3281,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.16/1.02      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
% 1.16/1.02      | ~ v1_tsep_1(sK2,sK3)
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK0)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK0)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_3279]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1254,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3071,plain,
% 1.16/1.02      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1254]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1260,plain,
% 1.16/1.02      ( ~ r1_tmap_1(X0_49,X1_49,X0_50,X1_50)
% 1.16/1.02      | r1_tmap_1(X0_49,X1_49,X2_50,X3_50)
% 1.16/1.02      | X2_50 != X0_50
% 1.16/1.02      | X3_50 != X1_50 ),
% 1.16/1.02      theory(equality) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2209,plain,
% 1.16/1.02      ( r1_tmap_1(sK2,sK0,X0_50,X1_50)
% 1.16/1.02      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.16/1.02      | X0_50 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.16/1.02      | X1_50 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1260]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2384,plain,
% 1.16/1.02      ( r1_tmap_1(sK2,sK0,X0_50,sK5)
% 1.16/1.02      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.16/1.02      | X0_50 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.16/1.02      | sK5 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2209]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2995,plain,
% 1.16/1.02      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
% 1.16/1.02      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.16/1.02      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.16/1.02      | sK5 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2384]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2711,plain,
% 1.16/1.02      ( k3_tmap_1(X0_49,X1_49,sK3,sK2,sK4) = k3_tmap_1(X0_49,X1_49,sK3,sK2,sK4) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1254]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2994,plain,
% 1.16/1.02      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2711]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2899,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,X0_49,sK4,sK5)
% 1.16/1.02      | r1_tmap_1(sK2,X0_49,k3_tmap_1(sK1,X0_49,sK3,sK2,sK4),sK5)
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(X0_49)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(X0_49)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | u1_struct_0(X0_49) != u1_struct_0(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2850]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2901,plain,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.16/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | v2_struct_0(sK3)
% 1.16/1.02      | v2_struct_0(sK1)
% 1.16/1.02      | v2_struct_0(sK0)
% 1.16/1.02      | v2_struct_0(sK2)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK0)
% 1.16/1.02      | ~ v2_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(sK0)
% 1.16/1.02      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.16/1.02      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2899]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1,plain,
% 1.16/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.16/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1251,plain,
% 1.16/1.02      ( ~ m1_pre_topc(X0_49,X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | l1_pre_topc(X0_49) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2398,plain,
% 1.16/1.02      ( ~ m1_pre_topc(sK3,X0_49)
% 1.16/1.02      | ~ l1_pre_topc(X0_49)
% 1.16/1.02      | l1_pre_topc(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1251]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2558,plain,
% 1.16/1.02      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2398]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_3,plain,
% 1.16/1.02      ( ~ v3_pre_topc(X0,X1)
% 1.16/1.02      | v3_pre_topc(X0,X2)
% 1.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.16/1.02      | ~ m1_pre_topc(X2,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f75]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1249,plain,
% 1.16/1.02      ( ~ v3_pre_topc(X0_50,X0_49)
% 1.16/1.02      | v3_pre_topc(X0_50,X1_49)
% 1.16/1.02      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X1_49)))
% 1.16/1.02      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 1.16/1.02      | ~ m1_pre_topc(X1_49,X0_49)
% 1.16/1.02      | ~ l1_pre_topc(X0_49) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2239,plain,
% 1.16/1.02      ( v3_pre_topc(u1_struct_0(sK2),X0_49)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_49)))
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.16/1.02      | ~ m1_pre_topc(X0_49,sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK1) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1249]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2419,plain,
% 1.16/1.02      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(sK2),sK1)
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.16/1.02      | ~ m1_pre_topc(sK3,sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK1) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2239]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2358,plain,
% 1.16/1.02      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1254]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1257,plain,
% 1.16/1.02      ( ~ m1_subset_1(X0_50,X1_50)
% 1.16/1.02      | m1_subset_1(X2_50,X3_50)
% 1.16/1.02      | X2_50 != X0_50
% 1.16/1.02      | X3_50 != X1_50 ),
% 1.16/1.02      theory(equality) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2194,plain,
% 1.16/1.02      ( m1_subset_1(X0_50,X1_50)
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.16/1.02      | X1_50 != u1_struct_0(sK2)
% 1.16/1.02      | X0_50 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1257]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2300,plain,
% 1.16/1.02      ( m1_subset_1(sK5,X0_50)
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.16/1.02      | X0_50 != u1_struct_0(sK2)
% 1.16/1.02      | sK5 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2194]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2357,plain,
% 1.16/1.02      ( m1_subset_1(sK5,u1_struct_0(sK2))
% 1.16/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.16/1.02      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.16/1.02      | sK5 != sK6 ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_2300]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_23,negated_conjecture,
% 1.16/1.02      ( m1_pre_topc(sK3,sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1237,negated_conjecture,
% 1.16/1.02      ( m1_pre_topc(sK3,sK1) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1868,plain,
% 1.16/1.02      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_0,plain,
% 1.16/1.02      ( ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | v2_pre_topc(X0) ),
% 1.16/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1252,plain,
% 1.16/1.02      ( ~ m1_pre_topc(X0_49,X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49)
% 1.16/1.02      | v2_pre_topc(X0_49) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1854,plain,
% 1.16/1.02      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 1.16/1.02      | l1_pre_topc(X1_49) != iProver_top
% 1.16/1.02      | v2_pre_topc(X1_49) != iProver_top
% 1.16/1.02      | v2_pre_topc(X0_49) = iProver_top ),
% 1.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2336,plain,
% 1.16/1.02      ( l1_pre_topc(sK1) != iProver_top
% 1.16/1.02      | v2_pre_topc(sK3) = iProver_top
% 1.16/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 1.16/1.02      inference(superposition,[status(thm)],[c_1868,c_1854]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2337,plain,
% 1.16/1.02      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK3) | ~ v2_pre_topc(sK1) ),
% 1.16/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2336]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_5,plain,
% 1.16/1.02      ( v1_tsep_1(X0,X1)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f77]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_7,plain,
% 1.16/1.02      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_178,plain,
% 1.16/1.02      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | v1_tsep_1(X0,X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5,c_7]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_179,plain,
% 1.16/1.02      ( v1_tsep_1(X0,X1)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(renaming,[status(thm)],[c_178]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1227,plain,
% 1.16/1.02      ( v1_tsep_1(X0_49,X1_49)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(X0_49),X1_49)
% 1.16/1.02      | ~ m1_pre_topc(X0_49,X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49)
% 1.16/1.02      | ~ v2_pre_topc(X1_49) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_179]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2165,plain,
% 1.16/1.02      ( v1_tsep_1(sK2,sK3)
% 1.16/1.02      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | ~ l1_pre_topc(sK3)
% 1.16/1.02      | ~ v2_pre_topc(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1227]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1248,plain,
% 1.16/1.02      ( m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49)))
% 1.16/1.02      | ~ m1_pre_topc(X0_49,X1_49)
% 1.16/1.02      | ~ l1_pre_topc(X1_49) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2142,plain,
% 1.16/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK1) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1248]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2139,plain,
% 1.16/1.02      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK3)
% 1.16/1.02      | ~ l1_pre_topc(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1248]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2128,plain,
% 1.16/1.02      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.16/1.02      inference(instantiation,[status(thm)],[c_1254]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_16,negated_conjecture,
% 1.16/1.02      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.16/1.02      inference(cnf_transformation,[],[f70]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1242,negated_conjecture,
% 1.16/1.02      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1863,plain,
% 1.16/1.02      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_14,negated_conjecture,
% 1.16/1.02      ( sK5 = sK6 ),
% 1.16/1.02      inference(cnf_transformation,[],[f72]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1244,negated_conjecture,
% 1.16/1.02      ( sK5 = sK6 ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1909,plain,
% 1.16/1.02      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.16/1.02      inference(light_normalisation,[status(thm)],[c_1863,c_1244]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2078,plain,
% 1.16/1.02      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.16/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1909]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_13,negated_conjecture,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.16/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1245,negated_conjecture,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.16/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1861,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 1.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_1920,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 1.16/1.02      inference(light_normalisation,[status(thm)],[c_1861,c_1244]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_2076,plain,
% 1.16/1.02      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.16/1.02      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.16/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1920]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_6,plain,
% 1.16/1.02      ( ~ v1_tsep_1(X0,X1)
% 1.16/1.02      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f78]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_171,plain,
% 1.16/1.02      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ v1_tsep_1(X0,X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(global_propositional_subsumption,[status(thm)],[c_6,c_7]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_172,plain,
% 1.16/1.02      ( ~ v1_tsep_1(X0,X1)
% 1.16/1.02      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1) ),
% 1.16/1.02      inference(renaming,[status(thm)],[c_171]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_19,negated_conjecture,
% 1.16/1.02      ( v1_tsep_1(sK2,sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_462,plain,
% 1.16/1.02      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.16/1.02      | ~ m1_pre_topc(X0,X1)
% 1.16/1.02      | ~ l1_pre_topc(X1)
% 1.16/1.02      | ~ v2_pre_topc(X1)
% 1.16/1.02      | sK1 != X1
% 1.16/1.02      | sK2 != X0 ),
% 1.16/1.02      inference(resolution_lifted,[status(thm)],[c_172,c_19]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_463,plain,
% 1.16/1.02      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 1.16/1.02      | ~ m1_pre_topc(sK2,sK1)
% 1.16/1.02      | ~ l1_pre_topc(sK1)
% 1.16/1.02      | ~ v2_pre_topc(sK1) ),
% 1.16/1.02      inference(unflattening,[status(thm)],[c_462]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_12,negated_conjecture,
% 1.16/1.02      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.16/1.02      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.16/1.02      inference(cnf_transformation,[],[f74]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_15,negated_conjecture,
% 1.16/1.02      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.16/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_17,negated_conjecture,
% 1.16/1.02      ( m1_pre_topc(sK2,sK3) ),
% 1.16/1.02      inference(cnf_transformation,[],[f69]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_20,negated_conjecture,
% 1.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 1.16/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_24,negated_conjecture,
% 1.16/1.02      ( ~ v2_struct_0(sK3) ),
% 1.16/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_25,negated_conjecture,
% 1.16/1.02      ( m1_pre_topc(sK2,sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_26,negated_conjecture,
% 1.16/1.02      ( ~ v2_struct_0(sK2) ),
% 1.16/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_27,negated_conjecture,
% 1.16/1.02      ( l1_pre_topc(sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_28,negated_conjecture,
% 1.16/1.02      ( v2_pre_topc(sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_29,negated_conjecture,
% 1.16/1.02      ( ~ v2_struct_0(sK1) ),
% 1.16/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_30,negated_conjecture,
% 1.16/1.02      ( l1_pre_topc(sK0) ),
% 1.16/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_31,negated_conjecture,
% 1.16/1.02      ( v2_pre_topc(sK0) ),
% 1.16/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(c_32,negated_conjecture,
% 1.16/1.02      ( ~ v2_struct_0(sK0) ),
% 1.16/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.16/1.02  
% 1.16/1.02  cnf(contradiction,plain,
% 1.16/1.02      ( $false ),
% 1.16/1.02      inference(minisat,
% 1.16/1.02                [status(thm)],
% 1.16/1.02                [c_3321,c_3281,c_3071,c_2995,c_2994,c_2901,c_2558,c_2419,
% 1.16/1.02                 c_2358,c_2357,c_2337,c_2165,c_2142,c_2139,c_2128,c_2078,
% 1.16/1.02                 c_2076,c_1244,c_463,c_12,c_13,c_15,c_16,c_17,c_20,c_23,
% 1.16/1.02                 c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 1.16/1.02  
% 1.16/1.02  
% 1.16/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.16/1.02  
% 1.16/1.02  ------                               Statistics
% 1.16/1.02  
% 1.16/1.02  ------ General
% 1.16/1.02  
% 1.16/1.02  abstr_ref_over_cycles:                  0
% 1.16/1.02  abstr_ref_under_cycles:                 0
% 1.16/1.02  gc_basic_clause_elim:                   0
% 1.16/1.02  forced_gc_time:                         0
% 1.16/1.02  parsing_time:                           0.011
% 1.16/1.02  unif_index_cands_time:                  0.
% 1.16/1.02  unif_index_add_time:                    0.
% 1.16/1.02  orderings_time:                         0.
% 1.16/1.02  out_proof_time:                         0.013
% 1.16/1.02  total_time:                             0.15
% 1.16/1.02  num_of_symbols:                         54
% 1.16/1.02  num_of_terms:                           2182
% 1.16/1.02  
% 1.16/1.02  ------ Preprocessing
% 1.16/1.02  
% 1.16/1.02  num_of_splits:                          0
% 1.16/1.02  num_of_split_atoms:                     0
% 1.16/1.02  num_of_reused_defs:                     0
% 1.16/1.02  num_eq_ax_congr_red:                    17
% 1.16/1.02  num_of_sem_filtered_clauses:            1
% 1.16/1.02  num_of_subtypes:                        2
% 1.16/1.02  monotx_restored_types:                  0
% 1.16/1.02  sat_num_of_epr_types:                   0
% 1.16/1.02  sat_num_of_non_cyclic_types:            0
% 1.16/1.02  sat_guarded_non_collapsed_types:        0
% 1.16/1.02  num_pure_diseq_elim:                    0
% 1.16/1.02  simp_replaced_by:                       0
% 1.16/1.02  res_preprocessed:                       132
% 1.16/1.02  prep_upred:                             0
% 1.16/1.02  prep_unflattend:                        21
% 1.16/1.02  smt_new_axioms:                         0
% 1.16/1.02  pred_elim_cands:                        8
% 1.16/1.02  pred_elim:                              2
% 1.16/1.02  pred_elim_cl:                           3
% 1.16/1.02  pred_elim_cycles:                       5
% 1.16/1.02  merged_defs:                            8
% 1.16/1.02  merged_defs_ncl:                        0
% 1.16/1.02  bin_hyper_res:                          8
% 1.16/1.02  prep_cycles:                            4
% 1.16/1.02  pred_elim_time:                         0.02
% 1.16/1.02  splitting_time:                         0.
% 1.16/1.02  sem_filter_time:                        0.
% 1.16/1.02  monotx_time:                            0.
% 1.16/1.02  subtype_inf_time:                       0.
% 1.16/1.02  
% 1.16/1.02  ------ Problem properties
% 1.16/1.02  
% 1.16/1.02  clauses:                                28
% 1.16/1.02  conjectures:                            18
% 1.16/1.02  epr:                                    16
% 1.16/1.02  horn:                                   25
% 1.16/1.02  ground:                                 18
% 1.16/1.02  unary:                                  16
% 1.16/1.02  binary:                                 2
% 1.16/1.02  lits:                                   90
% 1.16/1.02  lits_eq:                                5
% 1.16/1.02  fd_pure:                                0
% 1.16/1.02  fd_pseudo:                              0
% 1.16/1.02  fd_cond:                                0
% 1.16/1.02  fd_pseudo_cond:                         0
% 1.16/1.02  ac_symbols:                             0
% 1.16/1.02  
% 1.16/1.02  ------ Propositional Solver
% 1.16/1.02  
% 1.16/1.02  prop_solver_calls:                      28
% 1.16/1.02  prop_fast_solver_calls:                 1320
% 1.16/1.02  smt_solver_calls:                       0
% 1.16/1.02  smt_fast_solver_calls:                  0
% 1.16/1.02  prop_num_of_clauses:                    692
% 1.16/1.02  prop_preprocess_simplified:             3455
% 1.16/1.02  prop_fo_subsumed:                       45
% 1.16/1.02  prop_solver_time:                       0.
% 1.16/1.02  smt_solver_time:                        0.
% 1.16/1.02  smt_fast_solver_time:                   0.
% 1.16/1.02  prop_fast_solver_time:                  0.
% 1.16/1.02  prop_unsat_core_time:                   0.
% 1.16/1.02  
% 1.16/1.02  ------ QBF
% 1.16/1.02  
% 1.16/1.02  qbf_q_res:                              0
% 1.16/1.02  qbf_num_tautologies:                    0
% 1.16/1.02  qbf_prep_cycles:                        0
% 1.16/1.02  
% 1.16/1.02  ------ BMC1
% 1.16/1.02  
% 1.16/1.02  bmc1_current_bound:                     -1
% 1.16/1.02  bmc1_last_solved_bound:                 -1
% 1.16/1.02  bmc1_unsat_core_size:                   -1
% 1.16/1.02  bmc1_unsat_core_parents_size:           -1
% 1.16/1.02  bmc1_merge_next_fun:                    0
% 1.16/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.16/1.02  
% 1.16/1.02  ------ Instantiation
% 1.16/1.02  
% 1.16/1.02  inst_num_of_clauses:                    190
% 1.16/1.02  inst_num_in_passive:                    14
% 1.16/1.02  inst_num_in_active:                     167
% 1.16/1.02  inst_num_in_unprocessed:                9
% 1.16/1.02  inst_num_of_loops:                      199
% 1.16/1.02  inst_num_of_learning_restarts:          0
% 1.16/1.02  inst_num_moves_active_passive:          25
% 1.16/1.02  inst_lit_activity:                      0
% 1.16/1.02  inst_lit_activity_moves:                0
% 1.16/1.02  inst_num_tautologies:                   0
% 1.16/1.02  inst_num_prop_implied:                  0
% 1.16/1.02  inst_num_existing_simplified:           0
% 1.16/1.02  inst_num_eq_res_simplified:             0
% 1.16/1.02  inst_num_child_elim:                    0
% 1.16/1.02  inst_num_of_dismatching_blockings:      18
% 1.16/1.02  inst_num_of_non_proper_insts:           195
% 1.16/1.02  inst_num_of_duplicates:                 0
% 1.16/1.02  inst_inst_num_from_inst_to_res:         0
% 1.16/1.02  inst_dismatching_checking_time:         0.
% 1.16/1.02  
% 1.16/1.02  ------ Resolution
% 1.16/1.02  
% 1.16/1.02  res_num_of_clauses:                     0
% 1.16/1.02  res_num_in_passive:                     0
% 1.16/1.02  res_num_in_active:                      0
% 1.16/1.02  res_num_of_loops:                       136
% 1.16/1.02  res_forward_subset_subsumed:            37
% 1.16/1.02  res_backward_subset_subsumed:           4
% 1.16/1.02  res_forward_subsumed:                   0
% 1.16/1.02  res_backward_subsumed:                  0
% 1.16/1.02  res_forward_subsumption_resolution:     7
% 1.16/1.02  res_backward_subsumption_resolution:    0
% 1.16/1.02  res_clause_to_clause_subsumption:       187
% 1.16/1.02  res_orphan_elimination:                 0
% 1.16/1.02  res_tautology_del:                      65
% 1.16/1.02  res_num_eq_res_simplified:              0
% 1.16/1.02  res_num_sel_changes:                    0
% 1.16/1.02  res_moves_from_active_to_pass:          0
% 1.16/1.02  
% 1.16/1.02  ------ Superposition
% 1.16/1.02  
% 1.16/1.02  sup_time_total:                         0.
% 1.16/1.02  sup_time_generating:                    0.
% 1.16/1.02  sup_time_sim_full:                      0.
% 1.16/1.02  sup_time_sim_immed:                     0.
% 1.16/1.02  
% 1.16/1.02  sup_num_of_clauses:                     50
% 1.16/1.02  sup_num_in_active:                      38
% 1.16/1.02  sup_num_in_passive:                     12
% 1.16/1.02  sup_num_of_loops:                       38
% 1.16/1.02  sup_fw_superposition:                   14
% 1.16/1.02  sup_bw_superposition:                   10
% 1.16/1.02  sup_immediate_simplified:               0
% 1.16/1.02  sup_given_eliminated:                   0
% 1.16/1.02  comparisons_done:                       0
% 1.16/1.02  comparisons_avoided:                    0
% 1.16/1.02  
% 1.16/1.02  ------ Simplifications
% 1.16/1.02  
% 1.16/1.02  
% 1.16/1.02  sim_fw_subset_subsumed:                 0
% 1.16/1.02  sim_bw_subset_subsumed:                 0
% 1.16/1.02  sim_fw_subsumed:                        0
% 1.16/1.02  sim_bw_subsumed:                        0
% 1.16/1.02  sim_fw_subsumption_res:                 2
% 1.16/1.02  sim_bw_subsumption_res:                 0
% 1.16/1.02  sim_tautology_del:                      1
% 1.16/1.02  sim_eq_tautology_del:                   0
% 1.16/1.02  sim_eq_res_simp:                        0
% 1.16/1.02  sim_fw_demodulated:                     0
% 1.16/1.02  sim_bw_demodulated:                     0
% 1.16/1.02  sim_light_normalised:                   3
% 1.16/1.02  sim_joinable_taut:                      0
% 1.16/1.02  sim_joinable_simp:                      0
% 1.16/1.02  sim_ac_normalised:                      0
% 1.16/1.02  sim_smt_subsumption:                    0
% 1.16/1.02  
%------------------------------------------------------------------------------
