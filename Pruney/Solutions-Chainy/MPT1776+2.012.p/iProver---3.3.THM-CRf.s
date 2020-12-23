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
% DateTime   : Thu Dec  3 12:23:23 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  187 (1146 expanded)
%              Number of clauses        :  111 ( 193 expanded)
%              Number of leaves         :   18 ( 483 expanded)
%              Depth                    :   37
%              Number of atoms          : 1606 (22873 expanded)
%              Number of equality atoms :  403 (1667 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   46 (   7 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X0,X4,X6)
                                      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X0,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f53])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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

fof(f67,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f49,plain,(
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

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_181,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_725,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_181,c_23])).

cnf(c_726,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_730,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_24])).

cnf(c_731,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_730])).

cnf(c_1837,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK4),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK4,X4) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2282,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1837])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1168,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2069,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2070,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | ~ r1_tmap_1(sK3,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_2071,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2070])).

cnf(c_2951,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2282,c_43,c_2069,c_2071])).

cnf(c_2952,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2951])).

cnf(c_2973,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2952])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3170,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_35,c_36,c_37,c_47])).

cnf(c_3171,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3170])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1856,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1929,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1856,c_16])).

cnf(c_3187,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_1929])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1855,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1918,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1855,c_16])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_188,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_189,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_21,negated_conjecture,
    ( v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_465,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_21])).

cnf(c_466,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_468,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_30,c_29,c_27])).

cnf(c_478,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(sK2) != X6
    | sK1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_468])).

cnf(c_479,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_483,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | r1_tmap_1(X0,X1,X2,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_31,c_30,c_29])).

cnf(c_484,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_545,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X6)
    | X3 != X5
    | u1_struct_0(sK2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_484])).

cnf(c_546,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_656,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_546,c_23])).

cnf(c_657,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_24])).

cnf(c_662,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_661])).

cnf(c_1165,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_662])).

cnf(c_1839,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_44,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_50,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_658,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_2084,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2085,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_424,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_2146,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_2147,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2146])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2434,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2564,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_2565,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_2309,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2597,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_2598,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_2621,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1839,c_40,c_41,c_42,c_44,c_45,c_50,c_658,c_2085,c_2147,c_2565,c_2598])).

cnf(c_2622,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2621])).

cnf(c_2644,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2622])).

cnf(c_3064,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2644,c_43,c_44])).

cnf(c_3065,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3064])).

cnf(c_3084,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3065])).

cnf(c_3089,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3084,c_35,c_36,c_37,c_47])).

cnf(c_3090,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3089])).

cnf(c_3104,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_3090])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1853,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1887,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1853,c_16])).

cnf(c_3161,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3104,c_41,c_42,c_50,c_52,c_1887])).

cnf(c_3162,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3161])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1859,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3167,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3162,c_1859])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3187,c_3167,c_1887,c_52,c_50,c_44,c_42,c_41,c_40,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.85/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.03  
% 1.85/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/1.03  
% 1.85/1.03  ------  iProver source info
% 1.85/1.03  
% 1.85/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.85/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/1.03  git: non_committed_changes: false
% 1.85/1.03  git: last_make_outside_of_git: false
% 1.85/1.03  
% 1.85/1.03  ------ 
% 1.85/1.03  
% 1.85/1.03  ------ Input Options
% 1.85/1.03  
% 1.85/1.03  --out_options                           all
% 1.85/1.03  --tptp_safe_out                         true
% 1.85/1.03  --problem_path                          ""
% 1.85/1.03  --include_path                          ""
% 1.85/1.03  --clausifier                            res/vclausify_rel
% 1.85/1.03  --clausifier_options                    --mode clausify
% 1.85/1.03  --stdin                                 false
% 1.85/1.03  --stats_out                             all
% 1.85/1.03  
% 1.85/1.03  ------ General Options
% 1.85/1.03  
% 1.85/1.03  --fof                                   false
% 1.85/1.03  --time_out_real                         305.
% 1.85/1.03  --time_out_virtual                      -1.
% 1.85/1.03  --symbol_type_check                     false
% 1.85/1.03  --clausify_out                          false
% 1.85/1.03  --sig_cnt_out                           false
% 1.85/1.03  --trig_cnt_out                          false
% 1.85/1.03  --trig_cnt_out_tolerance                1.
% 1.85/1.03  --trig_cnt_out_sk_spl                   false
% 1.85/1.03  --abstr_cl_out                          false
% 1.85/1.03  
% 1.85/1.03  ------ Global Options
% 1.85/1.03  
% 1.85/1.03  --schedule                              default
% 1.85/1.03  --add_important_lit                     false
% 1.85/1.03  --prop_solver_per_cl                    1000
% 1.85/1.03  --min_unsat_core                        false
% 1.85/1.03  --soft_assumptions                      false
% 1.85/1.03  --soft_lemma_size                       3
% 1.85/1.03  --prop_impl_unit_size                   0
% 1.85/1.03  --prop_impl_unit                        []
% 1.85/1.03  --share_sel_clauses                     true
% 1.85/1.03  --reset_solvers                         false
% 1.85/1.03  --bc_imp_inh                            [conj_cone]
% 1.85/1.03  --conj_cone_tolerance                   3.
% 1.85/1.03  --extra_neg_conj                        none
% 1.85/1.03  --large_theory_mode                     true
% 1.85/1.03  --prolific_symb_bound                   200
% 1.85/1.03  --lt_threshold                          2000
% 1.85/1.03  --clause_weak_htbl                      true
% 1.85/1.03  --gc_record_bc_elim                     false
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing Options
% 1.85/1.03  
% 1.85/1.03  --preprocessing_flag                    true
% 1.85/1.03  --time_out_prep_mult                    0.1
% 1.85/1.03  --splitting_mode                        input
% 1.85/1.03  --splitting_grd                         true
% 1.85/1.03  --splitting_cvd                         false
% 1.85/1.03  --splitting_cvd_svl                     false
% 1.85/1.03  --splitting_nvd                         32
% 1.85/1.03  --sub_typing                            true
% 1.85/1.03  --prep_gs_sim                           true
% 1.85/1.03  --prep_unflatten                        true
% 1.85/1.03  --prep_res_sim                          true
% 1.85/1.03  --prep_upred                            true
% 1.85/1.03  --prep_sem_filter                       exhaustive
% 1.85/1.03  --prep_sem_filter_out                   false
% 1.85/1.03  --pred_elim                             true
% 1.85/1.03  --res_sim_input                         true
% 1.85/1.03  --eq_ax_congr_red                       true
% 1.85/1.03  --pure_diseq_elim                       true
% 1.85/1.03  --brand_transform                       false
% 1.85/1.03  --non_eq_to_eq                          false
% 1.85/1.03  --prep_def_merge                        true
% 1.85/1.03  --prep_def_merge_prop_impl              false
% 1.85/1.03  --prep_def_merge_mbd                    true
% 1.85/1.03  --prep_def_merge_tr_red                 false
% 1.85/1.03  --prep_def_merge_tr_cl                  false
% 1.85/1.03  --smt_preprocessing                     true
% 1.85/1.03  --smt_ac_axioms                         fast
% 1.85/1.03  --preprocessed_out                      false
% 1.85/1.03  --preprocessed_stats                    false
% 1.85/1.03  
% 1.85/1.03  ------ Abstraction refinement Options
% 1.85/1.03  
% 1.85/1.03  --abstr_ref                             []
% 1.85/1.03  --abstr_ref_prep                        false
% 1.85/1.03  --abstr_ref_until_sat                   false
% 1.85/1.03  --abstr_ref_sig_restrict                funpre
% 1.85/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.03  --abstr_ref_under                       []
% 1.85/1.03  
% 1.85/1.03  ------ SAT Options
% 1.85/1.03  
% 1.85/1.03  --sat_mode                              false
% 1.85/1.03  --sat_fm_restart_options                ""
% 1.85/1.03  --sat_gr_def                            false
% 1.85/1.03  --sat_epr_types                         true
% 1.85/1.03  --sat_non_cyclic_types                  false
% 1.85/1.03  --sat_finite_models                     false
% 1.85/1.03  --sat_fm_lemmas                         false
% 1.85/1.03  --sat_fm_prep                           false
% 1.85/1.03  --sat_fm_uc_incr                        true
% 1.85/1.03  --sat_out_model                         small
% 1.85/1.03  --sat_out_clauses                       false
% 1.85/1.03  
% 1.85/1.03  ------ QBF Options
% 1.85/1.03  
% 1.85/1.03  --qbf_mode                              false
% 1.85/1.03  --qbf_elim_univ                         false
% 1.85/1.03  --qbf_dom_inst                          none
% 1.85/1.03  --qbf_dom_pre_inst                      false
% 1.85/1.03  --qbf_sk_in                             false
% 1.85/1.03  --qbf_pred_elim                         true
% 1.85/1.03  --qbf_split                             512
% 1.85/1.03  
% 1.85/1.03  ------ BMC1 Options
% 1.85/1.03  
% 1.85/1.03  --bmc1_incremental                      false
% 1.85/1.03  --bmc1_axioms                           reachable_all
% 1.85/1.03  --bmc1_min_bound                        0
% 1.85/1.03  --bmc1_max_bound                        -1
% 1.85/1.03  --bmc1_max_bound_default                -1
% 1.85/1.03  --bmc1_symbol_reachability              true
% 1.85/1.03  --bmc1_property_lemmas                  false
% 1.85/1.03  --bmc1_k_induction                      false
% 1.85/1.03  --bmc1_non_equiv_states                 false
% 1.85/1.03  --bmc1_deadlock                         false
% 1.85/1.03  --bmc1_ucm                              false
% 1.85/1.03  --bmc1_add_unsat_core                   none
% 1.85/1.03  --bmc1_unsat_core_children              false
% 1.85/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.03  --bmc1_out_stat                         full
% 1.85/1.03  --bmc1_ground_init                      false
% 1.85/1.03  --bmc1_pre_inst_next_state              false
% 1.85/1.03  --bmc1_pre_inst_state                   false
% 1.85/1.03  --bmc1_pre_inst_reach_state             false
% 1.85/1.03  --bmc1_out_unsat_core                   false
% 1.85/1.03  --bmc1_aig_witness_out                  false
% 1.85/1.03  --bmc1_verbose                          false
% 1.85/1.03  --bmc1_dump_clauses_tptp                false
% 1.85/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.03  --bmc1_dump_file                        -
% 1.85/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.03  --bmc1_ucm_extend_mode                  1
% 1.85/1.03  --bmc1_ucm_init_mode                    2
% 1.85/1.03  --bmc1_ucm_cone_mode                    none
% 1.85/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.03  --bmc1_ucm_relax_model                  4
% 1.85/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.03  --bmc1_ucm_layered_model                none
% 1.85/1.03  --bmc1_ucm_max_lemma_size               10
% 1.85/1.03  
% 1.85/1.03  ------ AIG Options
% 1.85/1.03  
% 1.85/1.03  --aig_mode                              false
% 1.85/1.03  
% 1.85/1.03  ------ Instantiation Options
% 1.85/1.03  
% 1.85/1.03  --instantiation_flag                    true
% 1.85/1.03  --inst_sos_flag                         false
% 1.85/1.03  --inst_sos_phase                        true
% 1.85/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.03  --inst_lit_sel_side                     num_symb
% 1.85/1.03  --inst_solver_per_active                1400
% 1.85/1.03  --inst_solver_calls_frac                1.
% 1.85/1.03  --inst_passive_queue_type               priority_queues
% 1.85/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.03  --inst_passive_queues_freq              [25;2]
% 1.85/1.03  --inst_dismatching                      true
% 1.85/1.03  --inst_eager_unprocessed_to_passive     true
% 1.85/1.03  --inst_prop_sim_given                   true
% 1.85/1.03  --inst_prop_sim_new                     false
% 1.85/1.03  --inst_subs_new                         false
% 1.85/1.03  --inst_eq_res_simp                      false
% 1.85/1.03  --inst_subs_given                       false
% 1.85/1.03  --inst_orphan_elimination               true
% 1.85/1.03  --inst_learning_loop_flag               true
% 1.85/1.03  --inst_learning_start                   3000
% 1.85/1.03  --inst_learning_factor                  2
% 1.85/1.03  --inst_start_prop_sim_after_learn       3
% 1.85/1.03  --inst_sel_renew                        solver
% 1.85/1.03  --inst_lit_activity_flag                true
% 1.85/1.03  --inst_restr_to_given                   false
% 1.85/1.03  --inst_activity_threshold               500
% 1.85/1.03  --inst_out_proof                        true
% 1.85/1.03  
% 1.85/1.03  ------ Resolution Options
% 1.85/1.03  
% 1.85/1.03  --resolution_flag                       true
% 1.85/1.03  --res_lit_sel                           adaptive
% 1.85/1.03  --res_lit_sel_side                      none
% 1.85/1.03  --res_ordering                          kbo
% 1.85/1.03  --res_to_prop_solver                    active
% 1.85/1.03  --res_prop_simpl_new                    false
% 1.85/1.03  --res_prop_simpl_given                  true
% 1.85/1.03  --res_passive_queue_type                priority_queues
% 1.85/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.03  --res_passive_queues_freq               [15;5]
% 1.85/1.03  --res_forward_subs                      full
% 1.85/1.03  --res_backward_subs                     full
% 1.85/1.03  --res_forward_subs_resolution           true
% 1.85/1.03  --res_backward_subs_resolution          true
% 1.85/1.03  --res_orphan_elimination                true
% 1.85/1.03  --res_time_limit                        2.
% 1.85/1.03  --res_out_proof                         true
% 1.85/1.03  
% 1.85/1.03  ------ Superposition Options
% 1.85/1.03  
% 1.85/1.03  --superposition_flag                    true
% 1.85/1.03  --sup_passive_queue_type                priority_queues
% 1.85/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.03  --demod_completeness_check              fast
% 1.85/1.03  --demod_use_ground                      true
% 1.85/1.03  --sup_to_prop_solver                    passive
% 1.85/1.03  --sup_prop_simpl_new                    true
% 1.85/1.03  --sup_prop_simpl_given                  true
% 1.85/1.03  --sup_fun_splitting                     false
% 1.85/1.03  --sup_smt_interval                      50000
% 1.85/1.03  
% 1.85/1.03  ------ Superposition Simplification Setup
% 1.85/1.03  
% 1.85/1.03  --sup_indices_passive                   []
% 1.85/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_full_bw                           [BwDemod]
% 1.85/1.03  --sup_immed_triv                        [TrivRules]
% 1.85/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_immed_bw_main                     []
% 1.85/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.03  
% 1.85/1.03  ------ Combination Options
% 1.85/1.03  
% 1.85/1.03  --comb_res_mult                         3
% 1.85/1.03  --comb_sup_mult                         2
% 1.85/1.03  --comb_inst_mult                        10
% 1.85/1.03  
% 1.85/1.03  ------ Debug Options
% 1.85/1.03  
% 1.85/1.03  --dbg_backtrace                         false
% 1.85/1.03  --dbg_dump_prop_clauses                 false
% 1.85/1.03  --dbg_dump_prop_clauses_file            -
% 1.85/1.03  --dbg_out_stat                          false
% 1.85/1.03  ------ Parsing...
% 1.85/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/1.03  ------ Proving...
% 1.85/1.03  ------ Problem Properties 
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  clauses                                 25
% 1.85/1.03  conjectures                             17
% 1.85/1.03  EPR                                     15
% 1.85/1.03  Horn                                    21
% 1.85/1.03  unary                                   16
% 1.85/1.03  binary                                  2
% 1.85/1.03  lits                                    71
% 1.85/1.03  lits eq                                 6
% 1.85/1.03  fd_pure                                 0
% 1.85/1.03  fd_pseudo                               0
% 1.85/1.03  fd_cond                                 0
% 1.85/1.03  fd_pseudo_cond                          1
% 1.85/1.03  AC symbols                              0
% 1.85/1.03  
% 1.85/1.03  ------ Schedule dynamic 5 is on 
% 1.85/1.03  
% 1.85/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  ------ 
% 1.85/1.03  Current options:
% 1.85/1.03  ------ 
% 1.85/1.03  
% 1.85/1.03  ------ Input Options
% 1.85/1.03  
% 1.85/1.03  --out_options                           all
% 1.85/1.03  --tptp_safe_out                         true
% 1.85/1.03  --problem_path                          ""
% 1.85/1.03  --include_path                          ""
% 1.85/1.03  --clausifier                            res/vclausify_rel
% 1.85/1.03  --clausifier_options                    --mode clausify
% 1.85/1.03  --stdin                                 false
% 1.85/1.03  --stats_out                             all
% 1.85/1.03  
% 1.85/1.03  ------ General Options
% 1.85/1.03  
% 1.85/1.03  --fof                                   false
% 1.85/1.03  --time_out_real                         305.
% 1.85/1.03  --time_out_virtual                      -1.
% 1.85/1.03  --symbol_type_check                     false
% 1.85/1.03  --clausify_out                          false
% 1.85/1.03  --sig_cnt_out                           false
% 1.85/1.03  --trig_cnt_out                          false
% 1.85/1.03  --trig_cnt_out_tolerance                1.
% 1.85/1.03  --trig_cnt_out_sk_spl                   false
% 1.85/1.03  --abstr_cl_out                          false
% 1.85/1.03  
% 1.85/1.03  ------ Global Options
% 1.85/1.03  
% 1.85/1.03  --schedule                              default
% 1.85/1.03  --add_important_lit                     false
% 1.85/1.03  --prop_solver_per_cl                    1000
% 1.85/1.03  --min_unsat_core                        false
% 1.85/1.03  --soft_assumptions                      false
% 1.85/1.03  --soft_lemma_size                       3
% 1.85/1.03  --prop_impl_unit_size                   0
% 1.85/1.03  --prop_impl_unit                        []
% 1.85/1.03  --share_sel_clauses                     true
% 1.85/1.03  --reset_solvers                         false
% 1.85/1.03  --bc_imp_inh                            [conj_cone]
% 1.85/1.03  --conj_cone_tolerance                   3.
% 1.85/1.03  --extra_neg_conj                        none
% 1.85/1.03  --large_theory_mode                     true
% 1.85/1.03  --prolific_symb_bound                   200
% 1.85/1.03  --lt_threshold                          2000
% 1.85/1.03  --clause_weak_htbl                      true
% 1.85/1.03  --gc_record_bc_elim                     false
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing Options
% 1.85/1.03  
% 1.85/1.03  --preprocessing_flag                    true
% 1.85/1.03  --time_out_prep_mult                    0.1
% 1.85/1.03  --splitting_mode                        input
% 1.85/1.03  --splitting_grd                         true
% 1.85/1.03  --splitting_cvd                         false
% 1.85/1.03  --splitting_cvd_svl                     false
% 1.85/1.03  --splitting_nvd                         32
% 1.85/1.03  --sub_typing                            true
% 1.85/1.03  --prep_gs_sim                           true
% 1.85/1.03  --prep_unflatten                        true
% 1.85/1.03  --prep_res_sim                          true
% 1.85/1.03  --prep_upred                            true
% 1.85/1.03  --prep_sem_filter                       exhaustive
% 1.85/1.03  --prep_sem_filter_out                   false
% 1.85/1.03  --pred_elim                             true
% 1.85/1.03  --res_sim_input                         true
% 1.85/1.03  --eq_ax_congr_red                       true
% 1.85/1.03  --pure_diseq_elim                       true
% 1.85/1.03  --brand_transform                       false
% 1.85/1.03  --non_eq_to_eq                          false
% 1.85/1.03  --prep_def_merge                        true
% 1.85/1.03  --prep_def_merge_prop_impl              false
% 1.85/1.03  --prep_def_merge_mbd                    true
% 1.85/1.03  --prep_def_merge_tr_red                 false
% 1.85/1.03  --prep_def_merge_tr_cl                  false
% 1.85/1.03  --smt_preprocessing                     true
% 1.85/1.03  --smt_ac_axioms                         fast
% 1.85/1.03  --preprocessed_out                      false
% 1.85/1.03  --preprocessed_stats                    false
% 1.85/1.03  
% 1.85/1.03  ------ Abstraction refinement Options
% 1.85/1.03  
% 1.85/1.03  --abstr_ref                             []
% 1.85/1.03  --abstr_ref_prep                        false
% 1.85/1.03  --abstr_ref_until_sat                   false
% 1.85/1.03  --abstr_ref_sig_restrict                funpre
% 1.85/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.03  --abstr_ref_under                       []
% 1.85/1.03  
% 1.85/1.03  ------ SAT Options
% 1.85/1.03  
% 1.85/1.03  --sat_mode                              false
% 1.85/1.03  --sat_fm_restart_options                ""
% 1.85/1.03  --sat_gr_def                            false
% 1.85/1.03  --sat_epr_types                         true
% 1.85/1.03  --sat_non_cyclic_types                  false
% 1.85/1.03  --sat_finite_models                     false
% 1.85/1.03  --sat_fm_lemmas                         false
% 1.85/1.03  --sat_fm_prep                           false
% 1.85/1.03  --sat_fm_uc_incr                        true
% 1.85/1.03  --sat_out_model                         small
% 1.85/1.03  --sat_out_clauses                       false
% 1.85/1.03  
% 1.85/1.03  ------ QBF Options
% 1.85/1.03  
% 1.85/1.03  --qbf_mode                              false
% 1.85/1.03  --qbf_elim_univ                         false
% 1.85/1.03  --qbf_dom_inst                          none
% 1.85/1.03  --qbf_dom_pre_inst                      false
% 1.85/1.03  --qbf_sk_in                             false
% 1.85/1.03  --qbf_pred_elim                         true
% 1.85/1.03  --qbf_split                             512
% 1.85/1.03  
% 1.85/1.03  ------ BMC1 Options
% 1.85/1.03  
% 1.85/1.03  --bmc1_incremental                      false
% 1.85/1.03  --bmc1_axioms                           reachable_all
% 1.85/1.03  --bmc1_min_bound                        0
% 1.85/1.03  --bmc1_max_bound                        -1
% 1.85/1.03  --bmc1_max_bound_default                -1
% 1.85/1.03  --bmc1_symbol_reachability              true
% 1.85/1.03  --bmc1_property_lemmas                  false
% 1.85/1.03  --bmc1_k_induction                      false
% 1.85/1.03  --bmc1_non_equiv_states                 false
% 1.85/1.03  --bmc1_deadlock                         false
% 1.85/1.03  --bmc1_ucm                              false
% 1.85/1.03  --bmc1_add_unsat_core                   none
% 1.85/1.03  --bmc1_unsat_core_children              false
% 1.85/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.03  --bmc1_out_stat                         full
% 1.85/1.03  --bmc1_ground_init                      false
% 1.85/1.03  --bmc1_pre_inst_next_state              false
% 1.85/1.03  --bmc1_pre_inst_state                   false
% 1.85/1.03  --bmc1_pre_inst_reach_state             false
% 1.85/1.03  --bmc1_out_unsat_core                   false
% 1.85/1.03  --bmc1_aig_witness_out                  false
% 1.85/1.03  --bmc1_verbose                          false
% 1.85/1.03  --bmc1_dump_clauses_tptp                false
% 1.85/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.03  --bmc1_dump_file                        -
% 1.85/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.03  --bmc1_ucm_extend_mode                  1
% 1.85/1.03  --bmc1_ucm_init_mode                    2
% 1.85/1.03  --bmc1_ucm_cone_mode                    none
% 1.85/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.03  --bmc1_ucm_relax_model                  4
% 1.85/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.03  --bmc1_ucm_layered_model                none
% 1.85/1.03  --bmc1_ucm_max_lemma_size               10
% 1.85/1.03  
% 1.85/1.03  ------ AIG Options
% 1.85/1.03  
% 1.85/1.03  --aig_mode                              false
% 1.85/1.03  
% 1.85/1.03  ------ Instantiation Options
% 1.85/1.03  
% 1.85/1.03  --instantiation_flag                    true
% 1.85/1.03  --inst_sos_flag                         false
% 1.85/1.03  --inst_sos_phase                        true
% 1.85/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.03  --inst_lit_sel_side                     none
% 1.85/1.03  --inst_solver_per_active                1400
% 1.85/1.03  --inst_solver_calls_frac                1.
% 1.85/1.03  --inst_passive_queue_type               priority_queues
% 1.85/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.03  --inst_passive_queues_freq              [25;2]
% 1.85/1.03  --inst_dismatching                      true
% 1.85/1.03  --inst_eager_unprocessed_to_passive     true
% 1.85/1.03  --inst_prop_sim_given                   true
% 1.85/1.03  --inst_prop_sim_new                     false
% 1.85/1.03  --inst_subs_new                         false
% 1.85/1.03  --inst_eq_res_simp                      false
% 1.85/1.03  --inst_subs_given                       false
% 1.85/1.03  --inst_orphan_elimination               true
% 1.85/1.03  --inst_learning_loop_flag               true
% 1.85/1.03  --inst_learning_start                   3000
% 1.85/1.03  --inst_learning_factor                  2
% 1.85/1.03  --inst_start_prop_sim_after_learn       3
% 1.85/1.03  --inst_sel_renew                        solver
% 1.85/1.03  --inst_lit_activity_flag                true
% 1.85/1.03  --inst_restr_to_given                   false
% 1.85/1.03  --inst_activity_threshold               500
% 1.85/1.03  --inst_out_proof                        true
% 1.85/1.03  
% 1.85/1.03  ------ Resolution Options
% 1.85/1.03  
% 1.85/1.03  --resolution_flag                       false
% 1.85/1.03  --res_lit_sel                           adaptive
% 1.85/1.03  --res_lit_sel_side                      none
% 1.85/1.03  --res_ordering                          kbo
% 1.85/1.03  --res_to_prop_solver                    active
% 1.85/1.03  --res_prop_simpl_new                    false
% 1.85/1.03  --res_prop_simpl_given                  true
% 1.85/1.03  --res_passive_queue_type                priority_queues
% 1.85/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.03  --res_passive_queues_freq               [15;5]
% 1.85/1.03  --res_forward_subs                      full
% 1.85/1.03  --res_backward_subs                     full
% 1.85/1.03  --res_forward_subs_resolution           true
% 1.85/1.03  --res_backward_subs_resolution          true
% 1.85/1.03  --res_orphan_elimination                true
% 1.85/1.03  --res_time_limit                        2.
% 1.85/1.03  --res_out_proof                         true
% 1.85/1.03  
% 1.85/1.03  ------ Superposition Options
% 1.85/1.03  
% 1.85/1.03  --superposition_flag                    true
% 1.85/1.03  --sup_passive_queue_type                priority_queues
% 1.85/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.03  --demod_completeness_check              fast
% 1.85/1.03  --demod_use_ground                      true
% 1.85/1.03  --sup_to_prop_solver                    passive
% 1.85/1.03  --sup_prop_simpl_new                    true
% 1.85/1.03  --sup_prop_simpl_given                  true
% 1.85/1.03  --sup_fun_splitting                     false
% 1.85/1.03  --sup_smt_interval                      50000
% 1.85/1.03  
% 1.85/1.03  ------ Superposition Simplification Setup
% 1.85/1.03  
% 1.85/1.03  --sup_indices_passive                   []
% 1.85/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_full_bw                           [BwDemod]
% 1.85/1.03  --sup_immed_triv                        [TrivRules]
% 1.85/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_immed_bw_main                     []
% 1.85/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.03  
% 1.85/1.03  ------ Combination Options
% 1.85/1.03  
% 1.85/1.03  --comb_res_mult                         3
% 1.85/1.03  --comb_sup_mult                         2
% 1.85/1.03  --comb_inst_mult                        10
% 1.85/1.03  
% 1.85/1.03  ------ Debug Options
% 1.85/1.03  
% 1.85/1.03  --dbg_backtrace                         false
% 1.85/1.03  --dbg_dump_prop_clauses                 false
% 1.85/1.03  --dbg_dump_prop_clauses_file            -
% 1.85/1.03  --dbg_out_stat                          false
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  ------ Proving...
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  % SZS status Theorem for theBenchmark.p
% 1.85/1.03  
% 1.85/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/1.03  
% 1.85/1.03  fof(f9,axiom,(
% 1.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f23,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/1.03    inference(ennf_transformation,[],[f9])).
% 1.85/1.03  
% 1.85/1.03  fof(f24,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/1.03    inference(flattening,[],[f23])).
% 1.85/1.03  
% 1.85/1.03  fof(f31,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/1.03    inference(nnf_transformation,[],[f24])).
% 1.85/1.03  
% 1.85/1.03  fof(f54,plain,(
% 1.85/1.03    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f31])).
% 1.85/1.03  
% 1.85/1.03  fof(f84,plain,(
% 1.85/1.03    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(equality_resolution,[],[f54])).
% 1.85/1.03  
% 1.85/1.03  fof(f8,axiom,(
% 1.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f21,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/1.03    inference(ennf_transformation,[],[f8])).
% 1.85/1.03  
% 1.85/1.03  fof(f22,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/1.03    inference(flattening,[],[f21])).
% 1.85/1.03  
% 1.85/1.03  fof(f53,plain,(
% 1.85/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f22])).
% 1.85/1.03  
% 1.85/1.03  fof(f82,plain,(
% 1.85/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(equality_resolution,[],[f53])).
% 1.85/1.03  
% 1.85/1.03  fof(f10,conjecture,(
% 1.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f11,negated_conjecture,(
% 1.85/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.85/1.03    inference(negated_conjecture,[],[f10])).
% 1.85/1.03  
% 1.85/1.03  fof(f25,plain,(
% 1.85/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.85/1.03    inference(ennf_transformation,[],[f11])).
% 1.85/1.03  
% 1.85/1.03  fof(f26,plain,(
% 1.85/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.03    inference(flattening,[],[f25])).
% 1.85/1.03  
% 1.85/1.03  fof(f32,plain,(
% 1.85/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.03    inference(nnf_transformation,[],[f26])).
% 1.85/1.03  
% 1.85/1.03  fof(f33,plain,(
% 1.85/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.03    inference(flattening,[],[f32])).
% 1.85/1.03  
% 1.85/1.03  fof(f40,plain,(
% 1.85/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | r1_tmap_1(X3,X0,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f39,plain,(
% 1.85/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f38,plain,(
% 1.85/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X0,sK4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | r1_tmap_1(X3,X0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f37,plain,(
% 1.85/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | r1_tmap_1(sK3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f36,plain,(
% 1.85/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,X1) & v1_tsep_1(sK2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f35,plain,(
% 1.85/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f34,plain,(
% 1.85/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.85/1.03    introduced(choice_axiom,[])).
% 1.85/1.03  
% 1.85/1.03  fof(f41,plain,(
% 1.85/1.03    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.85/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f33,f40,f39,f38,f37,f36,f35,f34])).
% 1.85/1.03  
% 1.85/1.03  fof(f67,plain,(
% 1.85/1.03    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f66,plain,(
% 1.85/1.03    v1_funct_1(sK4)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f64,plain,(
% 1.85/1.03    ~v2_struct_0(sK3)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f56,plain,(
% 1.85/1.03    ~v2_struct_0(sK0)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f57,plain,(
% 1.85/1.03    v2_pre_topc(sK0)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f58,plain,(
% 1.85/1.03    l1_pre_topc(sK0)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f68,plain,(
% 1.85/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f76,plain,(
% 1.85/1.03    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f74,plain,(
% 1.85/1.03    sK5 = sK6),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f75,plain,(
% 1.85/1.03    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f2,axiom,(
% 1.85/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f12,plain,(
% 1.85/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.85/1.03    inference(ennf_transformation,[],[f2])).
% 1.85/1.03  
% 1.85/1.03  fof(f13,plain,(
% 1.85/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.85/1.03    inference(flattening,[],[f12])).
% 1.85/1.03  
% 1.85/1.03  fof(f45,plain,(
% 1.85/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f13])).
% 1.85/1.03  
% 1.85/1.03  fof(f55,plain,(
% 1.85/1.03    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f31])).
% 1.85/1.03  
% 1.85/1.03  fof(f83,plain,(
% 1.85/1.03    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X7) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(equality_resolution,[],[f55])).
% 1.85/1.03  
% 1.85/1.03  fof(f6,axiom,(
% 1.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f18,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.85/1.03    inference(ennf_transformation,[],[f6])).
% 1.85/1.03  
% 1.85/1.03  fof(f19,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/1.03    inference(flattening,[],[f18])).
% 1.85/1.03  
% 1.85/1.03  fof(f29,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/1.03    inference(nnf_transformation,[],[f19])).
% 1.85/1.03  
% 1.85/1.03  fof(f30,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/1.03    inference(flattening,[],[f29])).
% 1.85/1.03  
% 1.85/1.03  fof(f49,plain,(
% 1.85/1.03    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f30])).
% 1.85/1.03  
% 1.85/1.03  fof(f81,plain,(
% 1.85/1.03    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.85/1.03    inference(equality_resolution,[],[f49])).
% 1.85/1.03  
% 1.85/1.03  fof(f7,axiom,(
% 1.85/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f20,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.03    inference(ennf_transformation,[],[f7])).
% 1.85/1.03  
% 1.85/1.03  fof(f52,plain,(
% 1.85/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f20])).
% 1.85/1.03  
% 1.85/1.03  fof(f69,plain,(
% 1.85/1.03    v1_tsep_1(sK2,sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f60,plain,(
% 1.85/1.03    v2_pre_topc(sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f61,plain,(
% 1.85/1.03    l1_pre_topc(sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f63,plain,(
% 1.85/1.03    m1_pre_topc(sK2,sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f59,plain,(
% 1.85/1.03    ~v2_struct_0(sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f62,plain,(
% 1.85/1.03    ~v2_struct_0(sK2)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f65,plain,(
% 1.85/1.03    m1_pre_topc(sK3,sK1)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f71,plain,(
% 1.85/1.03    m1_pre_topc(sK2,sK3)),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f3,axiom,(
% 1.85/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f14,plain,(
% 1.85/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.85/1.03    inference(ennf_transformation,[],[f3])).
% 1.85/1.03  
% 1.85/1.03  fof(f46,plain,(
% 1.85/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f14])).
% 1.85/1.03  
% 1.85/1.03  fof(f5,axiom,(
% 1.85/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f16,plain,(
% 1.85/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.85/1.03    inference(ennf_transformation,[],[f5])).
% 1.85/1.03  
% 1.85/1.03  fof(f17,plain,(
% 1.85/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.85/1.03    inference(flattening,[],[f16])).
% 1.85/1.03  
% 1.85/1.03  fof(f48,plain,(
% 1.85/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f17])).
% 1.85/1.03  
% 1.85/1.03  fof(f4,axiom,(
% 1.85/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f15,plain,(
% 1.85/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.03    inference(ennf_transformation,[],[f4])).
% 1.85/1.03  
% 1.85/1.03  fof(f47,plain,(
% 1.85/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.03    inference(cnf_transformation,[],[f15])).
% 1.85/1.03  
% 1.85/1.03  fof(f73,plain,(
% 1.85/1.03    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f72,plain,(
% 1.85/1.03    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.85/1.03    inference(cnf_transformation,[],[f41])).
% 1.85/1.03  
% 1.85/1.03  fof(f1,axiom,(
% 1.85/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.03  
% 1.85/1.03  fof(f27,plain,(
% 1.85/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.03    inference(nnf_transformation,[],[f1])).
% 1.85/1.03  
% 1.85/1.03  fof(f28,plain,(
% 1.85/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.03    inference(flattening,[],[f27])).
% 1.85/1.03  
% 1.85/1.03  fof(f43,plain,(
% 1.85/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.85/1.03    inference(cnf_transformation,[],[f28])).
% 1.85/1.03  
% 1.85/1.03  fof(f77,plain,(
% 1.85/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.85/1.03    inference(equality_resolution,[],[f43])).
% 1.85/1.03  
% 1.85/1.03  cnf(c_13,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ v3_pre_topc(X6,X5)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ r2_hidden(X3,X6)
% 1.85/1.03      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5) ),
% 1.85/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_11,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X5)
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_180,plain,
% 1.85/1.03      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_13,c_11]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_181,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5) ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_180]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_23,negated_conjecture,
% 1.85/1.03      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 1.85/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_725,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5)
% 1.85/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | sK4 != X2 ),
% 1.85/1.03      inference(resolution_lifted,[status(thm)],[c_181,c_23]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_726,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.85/1.03      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.85/1.03      | ~ m1_pre_topc(X0,X3)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X3,X2)
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.85/1.03      | ~ v1_funct_1(sK4)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X2)
% 1.85/1.03      | v2_struct_0(X3)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X2)
% 1.85/1.03      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(unflattening,[status(thm)],[c_725]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_24,negated_conjecture,
% 1.85/1.03      ( v1_funct_1(sK4) ),
% 1.85/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_730,plain,
% 1.85/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_pre_topc(X3,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,X3)
% 1.85/1.03      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.85/1.03      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X2)
% 1.85/1.03      | v2_struct_0(X3)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X2)
% 1.85/1.03      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_726,c_24]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_731,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.85/1.03      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.85/1.03      | ~ m1_pre_topc(X3,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,X3)
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X2)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X3)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X2)
% 1.85/1.03      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_730]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1837,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK4),X4) = iProver_top
% 1.85/1.03      | r1_tmap_1(X0,X1,sK4,X4) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,X3) != iProver_top
% 1.85/1.03      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_pre_topc(X3) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(X3) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | l1_pre_topc(X3) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2282,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X2) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | v2_pre_topc(X2) != iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(sK3) = iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top
% 1.85/1.03      | l1_pre_topc(X2) != iProver_top ),
% 1.85/1.03      inference(equality_resolution,[status(thm)],[c_1837]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_26,negated_conjecture,
% 1.85/1.03      ( ~ v2_struct_0(sK3) ),
% 1.85/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_43,plain,
% 1.85/1.03      ( v2_struct_0(sK3) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1168,plain,( X0 = X0 ),theory(equality) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2069,plain,
% 1.85/1.03      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_1168]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2070,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 1.85/1.03      | ~ r1_tmap_1(sK3,X1,sK4,X3)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK3)
% 1.85/1.03      | ~ m1_pre_topc(sK3,X2)
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X2)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | v2_struct_0(sK3)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X2)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_731]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2071,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X2) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_pre_topc(X2) != iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(sK3) = iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top
% 1.85/1.03      | l1_pre_topc(X2) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2070]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2951,plain,
% 1.85/1.03      ( v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_pre_topc(X2) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,X2) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 1.85/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top
% 1.85/1.03      | l1_pre_topc(X2) != iProver_top ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_2282,c_43,c_2069,c_2071]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2952,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X2) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | v2_pre_topc(X2) != iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top
% 1.85/1.03      | l1_pre_topc(X2) != iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_2951]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2973,plain,
% 1.85/1.03      ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X1) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_pre_topc(sK0) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(sK0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 1.85/1.03      inference(equality_resolution,[status(thm)],[c_2952]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_34,negated_conjecture,
% 1.85/1.03      ( ~ v2_struct_0(sK0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_35,plain,
% 1.85/1.03      ( v2_struct_0(sK0) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_33,negated_conjecture,
% 1.85/1.03      ( v2_pre_topc(sK0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_36,plain,
% 1.85/1.03      ( v2_pre_topc(sK0) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_32,negated_conjecture,
% 1.85/1.03      ( l1_pre_topc(sK0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_37,plain,
% 1.85/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_22,negated_conjecture,
% 1.85/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 1.85/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_47,plain,
% 1.85/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3170,plain,
% 1.85/1.03      ( l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X1) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_2973,c_35,c_36,c_37,c_47]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3171,plain,
% 1.85/1.03      ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,X1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,X1) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_3170]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_14,negated_conjecture,
% 1.85/1.03      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.85/1.03      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.85/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1856,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_16,negated_conjecture,
% 1.85/1.03      ( sK5 = sK6 ),
% 1.85/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1929,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 1.85/1.03      inference(light_normalisation,[status(thm)],[c_1856,c_16]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3187,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | v2_pre_topc(sK1) != iProver_top
% 1.85/1.03      | v2_struct_0(sK1) = iProver_top
% 1.85/1.03      | v2_struct_0(sK2) = iProver_top
% 1.85/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 1.85/1.03      inference(superposition,[status(thm)],[c_3171,c_1929]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_15,negated_conjecture,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 1.85/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 1.85/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1855,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1918,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.85/1.03      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 1.85/1.03      inference(light_normalisation,[status(thm)],[c_1855,c_16]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3,plain,
% 1.85/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_12,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ v3_pre_topc(X6,X5)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ r2_hidden(X3,X6)
% 1.85/1.03      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5) ),
% 1.85/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_9,plain,
% 1.85/1.03      ( ~ v1_tsep_1(X0,X1)
% 1.85/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/1.03      | ~ m1_pre_topc(X0,X1)
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_10,plain,
% 1.85/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.85/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_188,plain,
% 1.85/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.85/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/1.03      | ~ v1_tsep_1(X0,X1)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_9,c_10]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_189,plain,
% 1.85/1.03      ( ~ v1_tsep_1(X0,X1)
% 1.85/1.03      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/1.03      | ~ m1_pre_topc(X0,X1)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_188]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_21,negated_conjecture,
% 1.85/1.03      ( v1_tsep_1(sK2,sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_465,plain,
% 1.85/1.03      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.85/1.03      | ~ m1_pre_topc(X0,X1)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | sK1 != X1
% 1.85/1.03      | sK2 != X0 ),
% 1.85/1.03      inference(resolution_lifted,[status(thm)],[c_189,c_21]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_466,plain,
% 1.85/1.03      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 1.85/1.03      | ~ m1_pre_topc(sK2,sK1)
% 1.85/1.03      | ~ v2_pre_topc(sK1)
% 1.85/1.03      | ~ l1_pre_topc(sK1) ),
% 1.85/1.03      inference(unflattening,[status(thm)],[c_465]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_30,negated_conjecture,
% 1.85/1.03      ( v2_pre_topc(sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_29,negated_conjecture,
% 1.85/1.03      ( l1_pre_topc(sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_27,negated_conjecture,
% 1.85/1.03      ( m1_pre_topc(sK2,sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_468,plain,
% 1.85/1.03      ( v3_pre_topc(u1_struct_0(sK2),sK1) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_466,c_30,c_29,c_27]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_478,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X4,X5)
% 1.85/1.03      | ~ m1_pre_topc(X0,X5)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ r2_hidden(X3,X6)
% 1.85/1.03      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X5)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X5)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(X5)
% 1.85/1.03      | u1_struct_0(sK2) != X6
% 1.85/1.03      | sK1 != X5 ),
% 1.85/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_468]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_479,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(sK1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | v2_struct_0(sK1)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ l1_pre_topc(sK1) ),
% 1.85/1.03      inference(unflattening,[status(thm)],[c_478]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_31,negated_conjecture,
% 1.85/1.03      ( ~ v2_struct_0(sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_483,plain,
% 1.85/1.03      ( ~ l1_pre_topc(X1)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_479,c_31,c_30,c_29]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_484,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1) ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_483]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_545,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_subset_1(X5,X6)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(X6)
% 1.85/1.03      | X3 != X5
% 1.85/1.03      | u1_struct_0(sK2) != X6 ),
% 1.85/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_484]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_546,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.85/1.03      inference(unflattening,[status(thm)],[c_545]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_656,plain,
% 1.85/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.85/1.03      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 1.85/1.03      | ~ m1_pre_topc(X4,X0)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X4,sK1)
% 1.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 1.85/1.03      | ~ v1_funct_1(X2)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X4)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 1.85/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | sK4 != X2 ),
% 1.85/1.03      inference(resolution_lifted,[status(thm)],[c_546,c_23]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_657,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 1.85/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X2,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 1.85/1.03      | ~ v1_funct_1(sK4)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 1.85/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(unflattening,[status(thm)],[c_656]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_661,plain,
% 1.85/1.03      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X2,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 1.85/1.03      | ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 1.85/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_657,c_24]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_662,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 1.85/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X2,sK1)
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 1.85/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_661]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1165,plain,
% 1.85/1.03      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 1.85/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 1.85/1.03      | ~ m1_pre_topc(X0,X2)
% 1.85/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.85/1.03      | ~ m1_pre_topc(X2,sK1)
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.85/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.85/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.85/1.03      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 1.85/1.03      | ~ v2_pre_topc(X1)
% 1.85/1.03      | v2_struct_0(X0)
% 1.85/1.03      | v2_struct_0(X1)
% 1.85/1.03      | v2_struct_0(X2)
% 1.85/1.03      | ~ l1_pre_topc(X1)
% 1.85/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | ~ sP0_iProver_split ),
% 1.85/1.03      inference(splitting,
% 1.85/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.85/1.03                [c_662]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1839,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | sP0_iProver_split != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_40,plain,
% 1.85/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_28,negated_conjecture,
% 1.85/1.03      ( ~ v2_struct_0(sK2) ),
% 1.85/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_41,plain,
% 1.85/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_42,plain,
% 1.85/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_25,negated_conjecture,
% 1.85/1.03      ( m1_pre_topc(sK3,sK1) ),
% 1.85/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_44,plain,
% 1.85/1.03      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_45,plain,
% 1.85/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_19,negated_conjecture,
% 1.85/1.03      ( m1_pre_topc(sK2,sK3) ),
% 1.85/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_50,plain,
% 1.85/1.03      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_658,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | v1_funct_1(sK4) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2084,plain,
% 1.85/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 1.85/1.03      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.85/1.03      | ~ l1_pre_topc(sK1) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2085,plain,
% 1.85/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.85/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_4,plain,
% 1.85/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_6,plain,
% 1.85/1.03      ( v2_struct_0(X0)
% 1.85/1.03      | ~ l1_struct_0(X0)
% 1.85/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.85/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_424,plain,
% 1.85/1.03      ( v2_struct_0(X0)
% 1.85/1.03      | ~ l1_pre_topc(X0)
% 1.85/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.85/1.03      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2146,plain,
% 1.85/1.03      ( v2_struct_0(sK2)
% 1.85/1.03      | ~ l1_pre_topc(sK2)
% 1.85/1.03      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_424]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2147,plain,
% 1.85/1.03      ( v2_struct_0(sK2) = iProver_top
% 1.85/1.03      | l1_pre_topc(sK2) != iProver_top
% 1.85/1.03      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2146]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_5,plain,
% 1.85/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2434,plain,
% 1.85/1.03      ( ~ m1_pre_topc(sK3,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK3) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2564,plain,
% 1.85/1.03      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_2434]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2565,plain,
% 1.85/1.03      ( m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/1.03      | l1_pre_topc(sK3) = iProver_top
% 1.85/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2309,plain,
% 1.85/1.03      ( ~ m1_pre_topc(sK2,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK2) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2597,plain,
% 1.85/1.03      ( ~ m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK3) | l1_pre_topc(sK2) ),
% 1.85/1.03      inference(instantiation,[status(thm)],[c_2309]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2598,plain,
% 1.85/1.03      ( m1_pre_topc(sK2,sK3) != iProver_top
% 1.85/1.03      | l1_pre_topc(sK3) != iProver_top
% 1.85/1.03      | l1_pre_topc(sK2) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2621,plain,
% 1.85/1.03      ( l1_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 1.85/1.03      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_1839,c_40,c_41,c_42,c_44,c_45,c_50,c_658,c_2085,
% 1.85/1.03                 c_2147,c_2565,c_2598]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2622,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 1.85/1.03      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 1.85/1.03      | m1_pre_topc(X2,X0) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(X2,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 1.85/1.03      | v2_pre_topc(X1) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X2) = iProver_top
% 1.85/1.03      | l1_pre_topc(X1) != iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_2621]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_2644,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK1) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(sK3) = iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top ),
% 1.85/1.03      inference(equality_resolution,[status(thm)],[c_2622]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3064,plain,
% 1.85/1.03      ( v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK1) != iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_2644,c_43,c_44]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3065,plain,
% 1.85/1.03      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 1.85/1.03      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X1,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 1.85/1.03      | v2_pre_topc(X0) != iProver_top
% 1.85/1.03      | v2_struct_0(X1) = iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | l1_pre_topc(X0) != iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_3064]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3084,plain,
% 1.85/1.03      ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | v2_pre_topc(sK0) != iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top
% 1.85/1.03      | v2_struct_0(sK0) = iProver_top
% 1.85/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 1.85/1.03      inference(equality_resolution,[status(thm)],[c_3065]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3089,plain,
% 1.85/1.03      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_3084,c_35,c_36,c_37,c_47]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3090,plain,
% 1.85/1.03      ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 1.85/1.03      | v2_struct_0(X0) = iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_3089]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3104,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.85/1.03      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.85/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 1.85/1.03      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.85/1.03      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | v2_struct_0(sK2) = iProver_top ),
% 1.85/1.03      inference(superposition,[status(thm)],[c_1918,c_3090]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_17,negated_conjecture,
% 1.85/1.03      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.85/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_52,plain,
% 1.85/1.03      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_18,negated_conjecture,
% 1.85/1.03      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.85/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1853,plain,
% 1.85/1.03      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1887,plain,
% 1.85/1.03      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.85/1.03      inference(light_normalisation,[status(thm)],[c_1853,c_16]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3161,plain,
% 1.85/1.03      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 1.85/1.03      | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top ),
% 1.85/1.03      inference(global_propositional_subsumption,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_3104,c_41,c_42,c_50,c_52,c_1887]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3162,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.85/1.03      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
% 1.85/1.03      inference(renaming,[status(thm)],[c_3161]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1,plain,
% 1.85/1.03      ( r1_tarski(X0,X0) ),
% 1.85/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_1859,plain,
% 1.85/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_3167,plain,
% 1.85/1.03      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top ),
% 1.85/1.03      inference(forward_subsumption_resolution,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_3162,c_1859]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_39,plain,
% 1.85/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(c_38,plain,
% 1.85/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 1.85/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.85/1.03  
% 1.85/1.03  cnf(contradiction,plain,
% 1.85/1.03      ( $false ),
% 1.85/1.03      inference(minisat,
% 1.85/1.03                [status(thm)],
% 1.85/1.03                [c_3187,c_3167,c_1887,c_52,c_50,c_44,c_42,c_41,c_40,c_39,
% 1.85/1.03                 c_38]) ).
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/1.03  
% 1.85/1.03  ------                               Statistics
% 1.85/1.03  
% 1.85/1.03  ------ General
% 1.85/1.03  
% 1.85/1.03  abstr_ref_over_cycles:                  0
% 1.85/1.03  abstr_ref_under_cycles:                 0
% 1.85/1.03  gc_basic_clause_elim:                   0
% 1.85/1.03  forced_gc_time:                         0
% 1.85/1.03  parsing_time:                           0.011
% 1.85/1.03  unif_index_cands_time:                  0.
% 1.85/1.03  unif_index_add_time:                    0.
% 1.85/1.03  orderings_time:                         0.
% 1.85/1.03  out_proof_time:                         0.023
% 1.85/1.03  total_time:                             0.11
% 1.85/1.03  num_of_symbols:                         57
% 1.85/1.03  num_of_terms:                           2055
% 1.85/1.03  
% 1.85/1.03  ------ Preprocessing
% 1.85/1.03  
% 1.85/1.03  num_of_splits:                          1
% 1.85/1.03  num_of_split_atoms:                     1
% 1.85/1.03  num_of_reused_defs:                     0
% 1.85/1.03  num_eq_ax_congr_red:                    5
% 1.85/1.03  num_of_sem_filtered_clauses:            1
% 1.85/1.03  num_of_subtypes:                        0
% 1.85/1.03  monotx_restored_types:                  0
% 1.85/1.03  sat_num_of_epr_types:                   0
% 1.85/1.03  sat_num_of_non_cyclic_types:            0
% 1.85/1.03  sat_guarded_non_collapsed_types:        0
% 1.85/1.03  num_pure_diseq_elim:                    0
% 1.85/1.03  simp_replaced_by:                       0
% 1.85/1.03  res_preprocessed:                       135
% 1.85/1.03  prep_upred:                             0
% 1.85/1.03  prep_unflattend:                        10
% 1.85/1.03  smt_new_axioms:                         0
% 1.85/1.03  pred_elim_cands:                        8
% 1.85/1.03  pred_elim:                              6
% 1.85/1.03  pred_elim_cl:                           8
% 1.85/1.03  pred_elim_cycles:                       10
% 1.85/1.03  merged_defs:                            8
% 1.85/1.03  merged_defs_ncl:                        0
% 1.85/1.03  bin_hyper_res:                          8
% 1.85/1.03  prep_cycles:                            4
% 1.85/1.03  pred_elim_time:                         0.013
% 1.85/1.03  splitting_time:                         0.
% 1.85/1.03  sem_filter_time:                        0.
% 1.85/1.03  monotx_time:                            0.
% 1.85/1.03  subtype_inf_time:                       0.
% 1.85/1.03  
% 1.85/1.03  ------ Problem properties
% 1.85/1.03  
% 1.85/1.03  clauses:                                25
% 1.85/1.03  conjectures:                            17
% 1.85/1.03  epr:                                    15
% 1.85/1.03  horn:                                   21
% 1.85/1.03  ground:                                 18
% 1.85/1.03  unary:                                  16
% 1.85/1.03  binary:                                 2
% 1.85/1.03  lits:                                   71
% 1.85/1.03  lits_eq:                                6
% 1.85/1.03  fd_pure:                                0
% 1.85/1.03  fd_pseudo:                              0
% 1.85/1.03  fd_cond:                                0
% 1.85/1.03  fd_pseudo_cond:                         1
% 1.85/1.03  ac_symbols:                             0
% 1.85/1.03  
% 1.85/1.03  ------ Propositional Solver
% 1.85/1.03  
% 1.85/1.03  prop_solver_calls:                      26
% 1.85/1.03  prop_fast_solver_calls:                 1329
% 1.85/1.03  smt_solver_calls:                       0
% 1.85/1.03  smt_fast_solver_calls:                  0
% 1.85/1.03  prop_num_of_clauses:                    715
% 1.85/1.03  prop_preprocess_simplified:             3621
% 1.85/1.03  prop_fo_subsumed:                       37
% 1.85/1.03  prop_solver_time:                       0.
% 1.85/1.03  smt_solver_time:                        0.
% 1.85/1.03  smt_fast_solver_time:                   0.
% 1.85/1.03  prop_fast_solver_time:                  0.
% 1.85/1.03  prop_unsat_core_time:                   0.
% 1.85/1.03  
% 1.85/1.03  ------ QBF
% 1.85/1.03  
% 1.85/1.03  qbf_q_res:                              0
% 1.85/1.03  qbf_num_tautologies:                    0
% 1.85/1.03  qbf_prep_cycles:                        0
% 1.85/1.03  
% 1.85/1.03  ------ BMC1
% 1.85/1.03  
% 1.85/1.03  bmc1_current_bound:                     -1
% 1.85/1.03  bmc1_last_solved_bound:                 -1
% 1.85/1.03  bmc1_unsat_core_size:                   -1
% 1.85/1.03  bmc1_unsat_core_parents_size:           -1
% 1.85/1.03  bmc1_merge_next_fun:                    0
% 1.85/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.85/1.03  
% 1.85/1.03  ------ Instantiation
% 1.85/1.03  
% 1.85/1.03  inst_num_of_clauses:                    207
% 1.85/1.03  inst_num_in_passive:                    12
% 1.85/1.03  inst_num_in_active:                     150
% 1.85/1.03  inst_num_in_unprocessed:                45
% 1.85/1.03  inst_num_of_loops:                      160
% 1.85/1.03  inst_num_of_learning_restarts:          0
% 1.85/1.03  inst_num_moves_active_passive:          8
% 1.85/1.03  inst_lit_activity:                      0
% 1.85/1.03  inst_lit_activity_moves:                0
% 1.85/1.03  inst_num_tautologies:                   0
% 1.85/1.03  inst_num_prop_implied:                  0
% 1.85/1.03  inst_num_existing_simplified:           0
% 1.85/1.03  inst_num_eq_res_simplified:             0
% 1.85/1.03  inst_num_child_elim:                    0
% 1.85/1.03  inst_num_of_dismatching_blockings:      12
% 1.85/1.03  inst_num_of_non_proper_insts:           237
% 1.85/1.03  inst_num_of_duplicates:                 0
% 1.85/1.03  inst_inst_num_from_inst_to_res:         0
% 1.85/1.03  inst_dismatching_checking_time:         0.
% 1.85/1.03  
% 1.85/1.03  ------ Resolution
% 1.85/1.03  
% 1.85/1.03  res_num_of_clauses:                     0
% 1.85/1.03  res_num_in_passive:                     0
% 1.85/1.03  res_num_in_active:                      0
% 1.85/1.03  res_num_of_loops:                       139
% 1.85/1.03  res_forward_subset_subsumed:            43
% 1.85/1.03  res_backward_subset_subsumed:           0
% 1.85/1.03  res_forward_subsumed:                   0
% 1.85/1.03  res_backward_subsumed:                  0
% 1.85/1.03  res_forward_subsumption_resolution:     0
% 1.85/1.03  res_backward_subsumption_resolution:    0
% 1.85/1.03  res_clause_to_clause_subsumption:       140
% 1.85/1.03  res_orphan_elimination:                 0
% 1.85/1.03  res_tautology_del:                      52
% 1.85/1.03  res_num_eq_res_simplified:              0
% 1.85/1.03  res_num_sel_changes:                    0
% 1.85/1.03  res_moves_from_active_to_pass:          0
% 1.85/1.03  
% 1.85/1.03  ------ Superposition
% 1.85/1.03  
% 1.85/1.03  sup_time_total:                         0.
% 1.85/1.03  sup_time_generating:                    0.
% 1.85/1.03  sup_time_sim_full:                      0.
% 1.85/1.03  sup_time_sim_immed:                     0.
% 1.85/1.03  
% 1.85/1.03  sup_num_of_clauses:                     34
% 1.85/1.03  sup_num_in_active:                      31
% 1.85/1.03  sup_num_in_passive:                     3
% 1.85/1.03  sup_num_of_loops:                       31
% 1.85/1.03  sup_fw_superposition:                   5
% 1.85/1.03  sup_bw_superposition:                   3
% 1.85/1.03  sup_immediate_simplified:               0
% 1.85/1.03  sup_given_eliminated:                   0
% 1.85/1.03  comparisons_done:                       0
% 1.85/1.03  comparisons_avoided:                    0
% 1.85/1.03  
% 1.85/1.03  ------ Simplifications
% 1.85/1.03  
% 1.85/1.03  
% 1.85/1.03  sim_fw_subset_subsumed:                 0
% 1.85/1.03  sim_bw_subset_subsumed:                 1
% 1.85/1.03  sim_fw_subsumed:                        0
% 1.85/1.03  sim_bw_subsumed:                        0
% 1.85/1.03  sim_fw_subsumption_res:                 1
% 1.85/1.03  sim_bw_subsumption_res:                 0
% 1.85/1.03  sim_tautology_del:                      2
% 1.85/1.03  sim_eq_tautology_del:                   0
% 1.85/1.03  sim_eq_res_simp:                        0
% 1.85/1.03  sim_fw_demodulated:                     0
% 1.85/1.03  sim_bw_demodulated:                     0
% 1.85/1.03  sim_light_normalised:                   3
% 1.85/1.03  sim_joinable_taut:                      0
% 1.85/1.03  sim_joinable_simp:                      0
% 1.85/1.03  sim_ac_normalised:                      0
% 1.85/1.03  sim_smt_subsumption:                    0
% 1.85/1.03  
%------------------------------------------------------------------------------
