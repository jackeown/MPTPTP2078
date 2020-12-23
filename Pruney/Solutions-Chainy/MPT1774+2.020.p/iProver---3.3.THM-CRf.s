%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:16 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 566 expanded)
%              Number of clauses        :  119 ( 127 expanded)
%              Number of leaves         :   21 ( 243 expanded)
%              Depth                    :   22
%              Number of atoms          : 1572 (11856 expanded)
%              Number of equality atoms :  229 ( 790 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f18])).

fof(f23,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f43])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X0,sK4,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X0,sK4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                            ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                    & m1_pre_topc(X2,X3)
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

fof(f26,plain,
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
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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

fof(f34,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f33,f32,f31,f30,f29,f28,f27,f26])).

fof(f62,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f42])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
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
    inference(equality_resolution,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f64,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1312,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
    | r1_tmap_1(X0_51,X1_51,X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_2566,plain,
    ( r1_tmap_1(sK2,sK0,X0_52,X1_52)
    | ~ r1_tmap_1(sK2,sK0,X2_52,sK6)
    | X0_52 != X2_52
    | X1_52 != sK6 ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_2993,plain,
    ( ~ r1_tmap_1(sK2,sK0,X0_52,sK6)
    | r1_tmap_1(sK2,sK0,X1_52,sK7)
    | X1_52 != X0_52
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_3488,plain,
    ( r1_tmap_1(sK2,sK0,X0_52,sK7)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_3959,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3488])).

cnf(c_3960,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK7 != sK6
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3959])).

cnf(c_1304,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_3728,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_7,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_392,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | sK5 != X6
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_393,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_439,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_393,c_5])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_582,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_439,c_20])).

cnf(c_583,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_587,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(sK5,X3)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_21])).

cnf(c_588,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_1275,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),sK6)
    | r1_tmap_1(X3_51,X1_51,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ r1_tarski(sK5,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_51)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK6,u1_struct_0(X3_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_588])).

cnf(c_2793,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),sK6)
    | r1_tmap_1(sK3,X1_51,sK4,sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK3,X2_51)
    | ~ r1_tarski(sK5,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_3002,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,X1_51)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_3342,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_3343,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3342])).

cnf(c_3345,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3343])).

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_6])).

cnf(c_159,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_654,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_20])).

cnf(c_655,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_659,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_21])).

cnf(c_660,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_659])).

cnf(c_701,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_660,c_5])).

cnf(c_1274,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_2227,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK3,X2_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_2561,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
    | ~ m1_pre_topc(sK3,X1_51)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_3089,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_3326,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3089])).

cnf(c_3328,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3326])).

cnf(c_2312,plain,
    ( r1_tmap_1(sK2,sK0,X0_52,X1_52)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | X1_52 != sK7 ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_2473,plain,
    ( r1_tmap_1(sK2,sK0,X0_52,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_3095,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2473])).

cnf(c_3096,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
    | sK6 != sK7
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3095])).

cnf(c_1303,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2826,plain,
    ( k3_tmap_1(X0_51,X1_51,sK3,sK2,sK4) = k3_tmap_1(X0_51,X1_51,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_3094,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_1305,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_2447,plain,
    ( X0_52 != X1_52
    | X0_52 = sK6
    | sK6 != X1_52 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_2643,plain,
    ( X0_52 = sK6
    | X0_52 != sK7
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2447])).

cnf(c_2780,plain,
    ( sK6 != sK7
    | sK7 = sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1299,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2500,plain,
    ( ~ m1_pre_topc(sK3,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_2632,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(c_2633,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2632])).

cnf(c_2436,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1308,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X1_52,X1_53)
    | X1_53 != X0_53
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_2282,plain,
    ( m1_subset_1(X0_52,X0_53)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_53 != u1_struct_0(sK2)
    | X0_52 != sK7 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2404,plain,
    ( m1_subset_1(sK6,X0_53)
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | X0_53 != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_2435,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_2437,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK7
    | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_2410,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1298,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2252,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_2398,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_2401,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1297,plain,
    ( ~ v3_pre_topc(X0_52,X0_51)
    | v3_pre_topc(X0_52,X1_51)
    | ~ m1_pre_topc(X1_51,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2307,plain,
    ( v3_pre_topc(sK5,X0_51)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_51,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2397,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2307])).

cnf(c_2399,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | v3_pre_topc(sK5,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_2226,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_11,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1293,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_207,c_12])).

cnf(c_464,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_465,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_52,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_51,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_49,plain,
    ( v3_pre_topc(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3960,c_3728,c_3345,c_3328,c_3096,c_3094,c_2780,c_2633,c_2436,c_2437,c_2410,c_2401,c_2399,c_2226,c_1293,c_465,c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_44,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.89/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/0.99  
% 1.89/0.99  ------  iProver source info
% 1.89/0.99  
% 1.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/0.99  git: non_committed_changes: false
% 1.89/0.99  git: last_make_outside_of_git: false
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     num_symb
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       true
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  ------ Parsing...
% 1.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/0.99  ------ Proving...
% 1.89/0.99  ------ Problem Properties 
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  clauses                                 28
% 1.89/0.99  conjectures                             20
% 1.89/0.99  EPR                                     15
% 1.89/0.99  Horn                                    25
% 1.89/0.99  unary                                   18
% 1.89/0.99  binary                                  4
% 1.89/0.99  lits                                    81
% 1.89/0.99  lits eq                                 5
% 1.89/0.99  fd_pure                                 0
% 1.89/0.99  fd_pseudo                               0
% 1.89/0.99  fd_cond                                 0
% 1.89/0.99  fd_pseudo_cond                          0
% 1.89/0.99  AC symbols                              0
% 1.89/0.99  
% 1.89/0.99  ------ Schedule dynamic 5 is on 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  Current options:
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     none
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       false
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ Proving...
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  % SZS status Theorem for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  fof(f7,axiom,(
% 1.89/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f18,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f7])).
% 1.89/0.99  
% 1.89/0.99  fof(f19,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f18])).
% 1.89/0.99  
% 1.89/0.99  fof(f23,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f19])).
% 1.89/0.99  
% 1.89/0.99  fof(f43,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f23])).
% 1.89/0.99  
% 1.89/0.99  fof(f69,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f43])).
% 1.89/0.99  
% 1.89/0.99  fof(f8,conjecture,(
% 1.89/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f9,negated_conjecture,(
% 1.89/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.89/0.99    inference(negated_conjecture,[],[f8])).
% 1.89/0.99  
% 1.89/0.99  fof(f20,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f9])).
% 1.89/0.99  
% 1.89/0.99  fof(f21,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f20])).
% 1.89/0.99  
% 1.89/0.99  fof(f24,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f21])).
% 1.89/0.99  
% 1.89/0.99  fof(f25,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f24])).
% 1.89/0.99  
% 1.89/0.99  fof(f33,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f32,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f31,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f30,plain,(
% 1.89/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f29,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f28,plain,(
% 1.89/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f27,plain,(
% 1.89/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f26,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f34,plain,(
% 1.89/0.99    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f33,f32,f31,f30,f29,f28,f27,f26])).
% 1.89/0.99  
% 1.89/0.99  fof(f62,plain,(
% 1.89/0.99    r2_hidden(sK6,sK5)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f5,axiom,(
% 1.89/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f14,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f5])).
% 1.89/0.99  
% 1.89/0.99  fof(f15,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.99    inference(flattening,[],[f14])).
% 1.89/0.99  
% 1.89/0.99  fof(f40,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f15])).
% 1.89/0.99  
% 1.89/0.99  fof(f55,plain,(
% 1.89/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f54,plain,(
% 1.89/0.99    v1_funct_1(sK4)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f42,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f23])).
% 1.89/0.99  
% 1.89/0.99  fof(f70,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f42])).
% 1.89/0.99  
% 1.89/0.99  fof(f6,axiom,(
% 1.89/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f16,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f6])).
% 1.89/0.99  
% 1.89/0.99  fof(f17,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f16])).
% 1.89/0.99  
% 1.89/0.99  fof(f41,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f17])).
% 1.89/0.99  
% 1.89/0.99  fof(f68,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f41])).
% 1.89/0.99  
% 1.89/0.99  fof(f2,axiom,(
% 1.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f10,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.89/0.99    inference(ennf_transformation,[],[f2])).
% 1.89/0.99  
% 1.89/0.99  fof(f37,plain,(
% 1.89/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f10])).
% 1.89/0.99  
% 1.89/0.99  fof(f3,axiom,(
% 1.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f11,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.89/0.99    inference(ennf_transformation,[],[f3])).
% 1.89/0.99  
% 1.89/0.99  fof(f38,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f11])).
% 1.89/0.99  
% 1.89/0.99  fof(f4,axiom,(
% 1.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f12,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.99    inference(ennf_transformation,[],[f4])).
% 1.89/0.99  
% 1.89/0.99  fof(f13,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.99    inference(flattening,[],[f12])).
% 1.89/0.99  
% 1.89/0.99  fof(f39,plain,(
% 1.89/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f13])).
% 1.89/0.99  
% 1.89/0.99  fof(f67,plain,(
% 1.89/0.99    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f39])).
% 1.89/0.99  
% 1.89/0.99  fof(f64,plain,(
% 1.89/0.99    sK6 = sK7),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f1,axiom,(
% 1.89/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f22,plain,(
% 1.89/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.89/0.99    inference(nnf_transformation,[],[f1])).
% 1.89/0.99  
% 1.89/0.99  fof(f36,plain,(
% 1.89/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f22])).
% 1.89/0.99  
% 1.89/0.99  fof(f63,plain,(
% 1.89/0.99    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f66,plain,(
% 1.89/0.99    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f65,plain,(
% 1.89/0.99    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f61,plain,(
% 1.89/0.99    v3_pre_topc(sK5,sK1)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f60,plain,(
% 1.89/0.99    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f59,plain,(
% 1.89/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f58,plain,(
% 1.89/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f57,plain,(
% 1.89/0.99    m1_pre_topc(sK2,sK3)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f56,plain,(
% 1.89/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f53,plain,(
% 1.89/0.99    m1_pre_topc(sK3,sK1)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f52,plain,(
% 1.89/0.99    ~v2_struct_0(sK3)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f50,plain,(
% 1.89/0.99    ~v2_struct_0(sK2)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f49,plain,(
% 1.89/0.99    l1_pre_topc(sK1)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f48,plain,(
% 1.89/0.99    v2_pre_topc(sK1)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f47,plain,(
% 1.89/0.99    ~v2_struct_0(sK1)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f46,plain,(
% 1.89/0.99    l1_pre_topc(sK0)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f45,plain,(
% 1.89/0.99    v2_pre_topc(sK0)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  fof(f44,plain,(
% 1.89/0.99    ~v2_struct_0(sK0)),
% 1.89/0.99    inference(cnf_transformation,[],[f34])).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1312,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
% 1.89/0.99      | r1_tmap_1(X0_51,X1_51,X2_52,X3_52)
% 1.89/0.99      | X2_52 != X0_52
% 1.89/0.99      | X3_52 != X1_52 ),
% 1.89/0.99      theory(equality) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2566,plain,
% 1.89/0.99      ( r1_tmap_1(sK2,sK0,X0_52,X1_52)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,X2_52,sK6)
% 1.89/0.99      | X0_52 != X2_52
% 1.89/0.99      | X1_52 != sK6 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2993,plain,
% 1.89/0.99      ( ~ r1_tmap_1(sK2,sK0,X0_52,sK6)
% 1.89/0.99      | r1_tmap_1(sK2,sK0,X1_52,sK7)
% 1.89/0.99      | X1_52 != X0_52
% 1.89/0.99      | sK7 != sK6 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2566]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3488,plain,
% 1.89/0.99      ( r1_tmap_1(sK2,sK0,X0_52,sK7)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.89/0.99      | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK7 != sK6 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2993]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3959,plain,
% 1.89/0.99      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.89/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK7 != sK6 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_3488]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3960,plain,
% 1.89/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK7 != sK6
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3959]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1304,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3728,plain,
% 1.89/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_7,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ r2_hidden(X3,X6)
% 1.89/0.99      | ~ v3_pre_topc(X6,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_13,negated_conjecture,
% 1.89/0.99      ( r2_hidden(sK6,sK5) ),
% 1.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_392,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ v3_pre_topc(X6,X0)
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | sK5 != X6
% 1.89/0.99      | sK6 != X3 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_393,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ v3_pre_topc(sK5,X0)
% 1.89/0.99      | ~ m1_pre_topc(X0,X4)
% 1.89/0.99      | ~ m1_pre_topc(X3,X0)
% 1.89/0.99      | ~ m1_pre_topc(X3,X4)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X4)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X4) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_5,plain,
% 1.89/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.89/0.99      | ~ m1_pre_topc(X2,X0)
% 1.89/0.99      | m1_pre_topc(X2,X1)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_439,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ v3_pre_topc(sK5,X0)
% 1.89/0.99      | ~ m1_pre_topc(X3,X0)
% 1.89/0.99      | ~ m1_pre_topc(X0,X4)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X4)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X4) ),
% 1.89/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_393,c_5]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_20,negated_conjecture,
% 1.89/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 1.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_582,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,X0)
% 1.89/0.99      | ~ m1_pre_topc(X3,X0)
% 1.89/0.99      | ~ m1_pre_topc(X0,X4)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X4)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X4)
% 1.89/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.89/0.99      | sK4 != X2 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_439,c_20]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_583,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.89/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,X3)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | ~ v1_funct_1(sK4)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_582]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_21,negated_conjecture,
% 1.89/0.99      ( v1_funct_1(sK4) ),
% 1.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_587,plain,
% 1.89/0.99      ( v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ v3_pre_topc(sK5,X3)
% 1.89/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.89/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(global_propositional_subsumption,
% 1.89/0.99                [status(thm)],
% 1.89/0.99                [c_583,c_21]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_588,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 1.89/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,X3)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(renaming,[status(thm)],[c_587]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1275,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),sK6)
% 1.89/0.99      | r1_tmap_1(X3_51,X1_51,sK4,sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,X3_51)
% 1.89/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 1.89/0.99      | ~ m1_pre_topc(X0_51,X3_51)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_51)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3_51))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(X2_51)
% 1.89/0.99      | v2_struct_0(X3_51)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X2_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X2_51)
% 1.89/0.99      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_588]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2793,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),sK6)
% 1.89/0.99      | r1_tmap_1(sK3,X1_51,sK4,sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,sK3)
% 1.89/0.99      | ~ m1_pre_topc(X0_51,sK3)
% 1.89/0.99      | ~ m1_pre_topc(sK3,X2_51)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(X2_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X2_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X2_51)
% 1.89/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1275]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3002,plain,
% 1.89/0.99      ( r1_tmap_1(sK3,X0_51,sK4,sK6)
% 1.89/0.99      | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,sK3)
% 1.89/0.99      | ~ m1_pre_topc(sK3,X1_51)
% 1.89/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | v2_struct_0(sK2)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X0_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X0_51)
% 1.89/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2793]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3342,plain,
% 1.89/0.99      ( r1_tmap_1(sK3,X0_51,sK4,sK6)
% 1.89/0.99      | ~ r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6)
% 1.89/0.99      | ~ v3_pre_topc(sK5,sK3)
% 1.89/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.89/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | v2_struct_0(sK1)
% 1.89/0.99      | v2_struct_0(sK2)
% 1.89/0.99      | ~ v2_pre_topc(X0_51)
% 1.89/0.99      | ~ v2_pre_topc(sK1)
% 1.89/0.99      | ~ l1_pre_topc(X0_51)
% 1.89/0.99      | ~ l1_pre_topc(sK1)
% 1.89/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_3002]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3343,plain,
% 1.89/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.89/0.99      | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK6) != iProver_top
% 1.89/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.89/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 1.89/0.99      | v2_struct_0(X0_51) = iProver_top
% 1.89/0.99      | v2_struct_0(sK3) = iProver_top
% 1.89/0.99      | v2_struct_0(sK1) = iProver_top
% 1.89/0.99      | v2_struct_0(sK2) = iProver_top
% 1.89/0.99      | v2_pre_topc(X0_51) != iProver_top
% 1.89/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.89/0.99      | l1_pre_topc(X0_51) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3342]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3345,plain,
% 1.89/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.89/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top
% 1.89/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.89/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 1.89/0.99      | v2_struct_0(sK3) = iProver_top
% 1.89/0.99      | v2_struct_0(sK1) = iProver_top
% 1.89/0.99      | v2_struct_0(sK0) = iProver_top
% 1.89/0.99      | v2_struct_0(sK2) = iProver_top
% 1.89/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.89/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_3343]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_8,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ r2_hidden(X3,X6)
% 1.89/0.99      | ~ v3_pre_topc(X6,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_6,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_158,plain,
% 1.89/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8,c_6]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_159,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5) ),
% 1.89/0.99      inference(renaming,[status(thm)],[c_158]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_654,plain,
% 1.89/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.89/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.89/0.99      | ~ m1_pre_topc(X0,X5)
% 1.89/0.99      | ~ m1_pre_topc(X4,X0)
% 1.89/0.99      | ~ m1_pre_topc(X4,X5)
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X5)
% 1.89/0.99      | v2_struct_0(X4)
% 1.89/0.99      | ~ v1_funct_1(X2)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X5)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X5)
% 1.89/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.89/0.99      | sK4 != X2 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_159,c_20]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_655,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ m1_pre_topc(X0,X2)
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v1_funct_1(sK4)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_654]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_659,plain,
% 1.89/0.99      ( v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_pre_topc(X0,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.89/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(global_propositional_subsumption,
% 1.89/0.99                [status(thm)],
% 1.89/0.99                [c_655,c_21]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_660,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ m1_pre_topc(X0,X2)
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(renaming,[status(thm)],[c_659]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_701,plain,
% 1.89/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 1.89/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 1.89/0.99      | ~ m1_pre_topc(X3,X2)
% 1.89/0.99      | ~ m1_pre_topc(X0,X3)
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | v2_struct_0(X1)
% 1.89/0.99      | v2_struct_0(X2)
% 1.89/0.99      | v2_struct_0(X3)
% 1.89/0.99      | ~ v2_pre_topc(X1)
% 1.89/0.99      | ~ v2_pre_topc(X2)
% 1.89/0.99      | ~ l1_pre_topc(X1)
% 1.89/0.99      | ~ l1_pre_topc(X2)
% 1.89/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_660,c_5]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1274,plain,
% 1.89/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
% 1.89/0.99      | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
% 1.89/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 1.89/0.99      | ~ m1_pre_topc(X0_51,X3_51)
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(X2_51)
% 1.89/0.99      | v2_struct_0(X3_51)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X2_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X2_51)
% 1.89/0.99      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_701]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2227,plain,
% 1.89/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
% 1.89/0.99      | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 1.89/0.99      | ~ m1_pre_topc(X0_51,sK3)
% 1.89/0.99      | ~ m1_pre_topc(sK3,X2_51)
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(X2_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X2_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X2_51)
% 1.89/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1274]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2561,plain,
% 1.89/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 1.89/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
% 1.89/0.99      | ~ m1_pre_topc(sK3,X1_51)
% 1.89/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(X1_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | v2_struct_0(sK2)
% 1.89/0.99      | ~ v2_pre_topc(X1_51)
% 1.89/0.99      | ~ v2_pre_topc(X0_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X0_51)
% 1.89/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2227]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3089,plain,
% 1.89/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 1.89/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
% 1.89/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.89/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 1.89/0.99      | v2_struct_0(X0_51)
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | v2_struct_0(sK1)
% 1.89/0.99      | v2_struct_0(sK2)
% 1.89/0.99      | ~ v2_pre_topc(X0_51)
% 1.89/0.99      | ~ v2_pre_topc(sK1)
% 1.89/0.99      | ~ l1_pre_topc(X0_51)
% 1.89/0.99      | ~ l1_pre_topc(sK1)
% 1.89/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2561]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3326,plain,
% 1.89/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.89/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.89/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.89/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
% 1.89/0.99      | v2_struct_0(sK3)
% 1.89/0.99      | v2_struct_0(sK1)
% 1.89/0.99      | v2_struct_0(sK0)
% 1.89/0.99      | v2_struct_0(sK2)
% 1.89/0.99      | ~ v2_pre_topc(sK1)
% 1.89/0.99      | ~ v2_pre_topc(sK0)
% 1.89/0.99      | ~ l1_pre_topc(sK1)
% 1.89/0.99      | ~ l1_pre_topc(sK0)
% 1.89/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_3089]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3328,plain,
% 1.89/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.89/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.89/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
% 1.89/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 1.89/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 1.89/0.99      | v2_struct_0(sK3) = iProver_top
% 1.89/0.99      | v2_struct_0(sK1) = iProver_top
% 1.89/0.99      | v2_struct_0(sK0) = iProver_top
% 1.89/0.99      | v2_struct_0(sK2) = iProver_top
% 1.89/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.89/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3326]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2312,plain,
% 1.89/0.99      ( r1_tmap_1(sK2,sK0,X0_52,X1_52)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.89/0.99      | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | X1_52 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2473,plain,
% 1.89/0.99      ( r1_tmap_1(sK2,sK0,X0_52,sK6)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.89/0.99      | X0_52 != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK6 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2312]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3095,plain,
% 1.89/0.99      ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
% 1.89/0.99      | k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK6 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2473]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3096,plain,
% 1.89/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k3_tmap_1(sK1,sK0,sK3,sK2,sK4)
% 1.89/0.99      | sK6 != sK7
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3095]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1303,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2826,plain,
% 1.89/0.99      ( k3_tmap_1(X0_51,X1_51,sK3,sK2,sK4) = k3_tmap_1(X0_51,X1_51,sK3,sK2,sK4) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3094,plain,
% 1.89/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k3_tmap_1(sK1,sK0,sK3,sK2,sK4) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2826]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1305,plain,
% 1.89/0.99      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 1.89/0.99      theory(equality) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2447,plain,
% 1.89/0.99      ( X0_52 != X1_52 | X0_52 = sK6 | sK6 != X1_52 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2643,plain,
% 1.89/0.99      ( X0_52 = sK6 | X0_52 != sK7 | sK6 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2447]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2780,plain,
% 1.89/0.99      ( sK6 != sK7 | sK7 = sK6 | sK7 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2643]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2,plain,
% 1.89/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1299,plain,
% 1.89/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 1.89/0.99      | ~ l1_pre_topc(X1_51)
% 1.89/0.99      | l1_pre_topc(X0_51) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2500,plain,
% 1.89/0.99      ( ~ m1_pre_topc(sK3,X0_51)
% 1.89/0.99      | ~ l1_pre_topc(X0_51)
% 1.89/0.99      | l1_pre_topc(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1299]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2632,plain,
% 1.89/0.99      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2500]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2633,plain,
% 1.89/0.99      ( m1_pre_topc(sK3,sK1) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK3) = iProver_top
% 1.89/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_2632]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2436,plain,
% 1.89/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1308,plain,
% 1.89/0.99      ( ~ m1_subset_1(X0_52,X0_53)
% 1.89/0.99      | m1_subset_1(X1_52,X1_53)
% 1.89/0.99      | X1_53 != X0_53
% 1.89/0.99      | X1_52 != X0_52 ),
% 1.89/0.99      theory(equality) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2282,plain,
% 1.89/0.99      ( m1_subset_1(X0_52,X0_53)
% 1.89/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.89/0.99      | X0_53 != u1_struct_0(sK2)
% 1.89/0.99      | X0_52 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1308]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2404,plain,
% 1.89/0.99      ( m1_subset_1(sK6,X0_53)
% 1.89/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.89/0.99      | X0_53 != u1_struct_0(sK2)
% 1.89/0.99      | sK6 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2282]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2435,plain,
% 1.89/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2))
% 1.89/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 1.89/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.89/0.99      | sK6 != sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2404]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2437,plain,
% 1.89/0.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.89/0.99      | sK6 != sK7
% 1.89/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top
% 1.89/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2410,plain,
% 1.89/0.99      ( sK7 = sK7 ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3,plain,
% 1.89/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1298,plain,
% 1.89/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 1.89/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
% 1.89/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
% 1.89/0.99      | ~ l1_pre_topc(X1_51) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2252,plain,
% 1.89/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.89/0.99      | ~ l1_pre_topc(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1298]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2398,plain,
% 1.89/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.89/0.99      | ~ l1_pre_topc(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2252]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2401,plain,
% 1.89/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_4,plain,
% 1.89/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.89/0.99      | v3_pre_topc(X0,X2)
% 1.89/0.99      | ~ m1_pre_topc(X2,X1)
% 1.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.89/0.99      | ~ l1_pre_topc(X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1297,plain,
% 1.89/0.99      ( ~ v3_pre_topc(X0_52,X0_51)
% 1.89/0.99      | v3_pre_topc(X0_52,X1_51)
% 1.89/0.99      | ~ m1_pre_topc(X1_51,X0_51)
% 1.89/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
% 1.89/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
% 1.89/0.99      | ~ l1_pre_topc(X0_51) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2307,plain,
% 1.89/0.99      ( v3_pre_topc(sK5,X0_51)
% 1.89/0.99      | ~ v3_pre_topc(sK5,sK1)
% 1.89/0.99      | ~ m1_pre_topc(X0_51,sK1)
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51)))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.89/0.99      | ~ l1_pre_topc(sK1) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1297]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2397,plain,
% 1.89/0.99      ( v3_pre_topc(sK5,sK3)
% 1.89/0.99      | ~ v3_pre_topc(sK5,sK1)
% 1.89/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.89/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.89/0.99      | ~ l1_pre_topc(sK1) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2307]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2399,plain,
% 1.89/0.99      ( v3_pre_topc(sK5,sK3) = iProver_top
% 1.89/0.99      | v3_pre_topc(sK5,sK1) != iProver_top
% 1.89/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.89/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.89/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2226,plain,
% 1.89/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_11,negated_conjecture,
% 1.89/0.99      ( sK6 = sK7 ),
% 1.89/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1293,negated_conjecture,
% 1.89/0.99      ( sK6 = sK7 ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_0,plain,
% 1.89/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.89/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_207,plain,
% 1.89/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.89/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_12,negated_conjecture,
% 1.89/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.89/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_463,plain,
% 1.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.89/0.99      | u1_struct_0(sK2) != X1
% 1.89/0.99      | sK5 != X0 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_207,c_12]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_464,plain,
% 1.89/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_463]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_465,plain,
% 1.89/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_9,negated_conjecture,
% 1.89/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.89/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 1.89/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_53,plain,
% 1.89/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_10,negated_conjecture,
% 1.89/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 1.89/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 1.89/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_52,plain,
% 1.89/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 1.89/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_51,plain,
% 1.89/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_14,negated_conjecture,
% 1.89/1.00      ( v3_pre_topc(sK5,sK1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_49,plain,
% 1.89/1.00      ( v3_pre_topc(sK5,sK1) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_15,negated_conjecture,
% 1.89/1.00      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 1.89/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_48,plain,
% 1.89/1.00      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_16,negated_conjecture,
% 1.89/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.89/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_47,plain,
% 1.89/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_17,negated_conjecture,
% 1.89/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.89/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_46,plain,
% 1.89/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_18,negated_conjecture,
% 1.89/1.00      ( m1_pre_topc(sK2,sK3) ),
% 1.89/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_45,plain,
% 1.89/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_19,negated_conjecture,
% 1.89/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 1.89/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_44,plain,
% 1.89/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_22,negated_conjecture,
% 1.89/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_41,plain,
% 1.89/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_23,negated_conjecture,
% 1.89/1.00      ( ~ v2_struct_0(sK3) ),
% 1.89/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_40,plain,
% 1.89/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_25,negated_conjecture,
% 1.89/1.00      ( ~ v2_struct_0(sK2) ),
% 1.89/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_38,plain,
% 1.89/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_26,negated_conjecture,
% 1.89/1.00      ( l1_pre_topc(sK1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_37,plain,
% 1.89/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_27,negated_conjecture,
% 1.89/1.00      ( v2_pre_topc(sK1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_36,plain,
% 1.89/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_28,negated_conjecture,
% 1.89/1.00      ( ~ v2_struct_0(sK1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_35,plain,
% 1.89/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_29,negated_conjecture,
% 1.89/1.00      ( l1_pre_topc(sK0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_34,plain,
% 1.89/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_30,negated_conjecture,
% 1.89/1.00      ( v2_pre_topc(sK0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_33,plain,
% 1.89/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_31,negated_conjecture,
% 1.89/1.00      ( ~ v2_struct_0(sK0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_32,plain,
% 1.89/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(contradiction,plain,
% 1.89/1.00      ( $false ),
% 1.89/1.00      inference(minisat,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_3960,c_3728,c_3345,c_3328,c_3096,c_3094,c_2780,c_2633,
% 1.89/1.00                 c_2436,c_2437,c_2410,c_2401,c_2399,c_2226,c_1293,c_465,
% 1.89/1.00                 c_53,c_52,c_51,c_49,c_48,c_47,c_46,c_45,c_44,c_41,c_40,
% 1.89/1.00                 c_38,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 1.89/1.00  
% 1.89/1.00  
% 1.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/1.00  
% 1.89/1.00  ------                               Statistics
% 1.89/1.00  
% 1.89/1.00  ------ General
% 1.89/1.00  
% 1.89/1.00  abstr_ref_over_cycles:                  0
% 1.89/1.00  abstr_ref_under_cycles:                 0
% 1.89/1.00  gc_basic_clause_elim:                   0
% 1.89/1.00  forced_gc_time:                         0
% 1.89/1.00  parsing_time:                           0.012
% 1.89/1.00  unif_index_cands_time:                  0.
% 1.89/1.00  unif_index_add_time:                    0.
% 1.89/1.00  orderings_time:                         0.
% 1.89/1.00  out_proof_time:                         0.012
% 1.89/1.00  total_time:                             0.161
% 1.89/1.00  num_of_symbols:                         57
% 1.89/1.00  num_of_terms:                           2591
% 1.89/1.00  
% 1.89/1.00  ------ Preprocessing
% 1.89/1.00  
% 1.89/1.00  num_of_splits:                          0
% 1.89/1.00  num_of_split_atoms:                     0
% 1.89/1.00  num_of_reused_defs:                     0
% 1.89/1.00  num_eq_ax_congr_red:                    13
% 1.89/1.00  num_of_sem_filtered_clauses:            1
% 1.89/1.00  num_of_subtypes:                        3
% 1.89/1.00  monotx_restored_types:                  0
% 1.89/1.00  sat_num_of_epr_types:                   0
% 1.89/1.00  sat_num_of_non_cyclic_types:            0
% 1.89/1.00  sat_guarded_non_collapsed_types:        0
% 1.89/1.00  num_pure_diseq_elim:                    0
% 1.89/1.00  simp_replaced_by:                       0
% 1.89/1.00  res_preprocessed:                       139
% 1.89/1.00  prep_upred:                             0
% 1.89/1.00  prep_unflattend:                        17
% 1.89/1.00  smt_new_axioms:                         0
% 1.89/1.00  pred_elim_cands:                        8
% 1.89/1.00  pred_elim:                              3
% 1.89/1.00  pred_elim_cl:                           4
% 1.89/1.00  pred_elim_cycles:                       6
% 1.89/1.00  merged_defs:                            16
% 1.89/1.00  merged_defs_ncl:                        0
% 1.89/1.00  bin_hyper_res:                          16
% 1.89/1.00  prep_cycles:                            4
% 1.89/1.00  pred_elim_time:                         0.024
% 1.89/1.00  splitting_time:                         0.
% 1.89/1.00  sem_filter_time:                        0.
% 1.89/1.00  monotx_time:                            0.
% 1.89/1.00  subtype_inf_time:                       0.
% 1.89/1.00  
% 1.89/1.00  ------ Problem properties
% 1.89/1.00  
% 1.89/1.00  clauses:                                28
% 1.89/1.00  conjectures:                            20
% 1.89/1.00  epr:                                    15
% 1.89/1.00  horn:                                   25
% 1.89/1.00  ground:                                 20
% 1.89/1.00  unary:                                  18
% 1.89/1.00  binary:                                 4
% 1.89/1.00  lits:                                   81
% 1.89/1.00  lits_eq:                                5
% 1.89/1.00  fd_pure:                                0
% 1.89/1.00  fd_pseudo:                              0
% 1.89/1.00  fd_cond:                                0
% 1.89/1.00  fd_pseudo_cond:                         0
% 1.89/1.00  ac_symbols:                             0
% 1.89/1.00  
% 1.89/1.00  ------ Propositional Solver
% 1.89/1.00  
% 1.89/1.00  prop_solver_calls:                      27
% 1.89/1.00  prop_fast_solver_calls:                 1300
% 1.89/1.00  smt_solver_calls:                       0
% 1.89/1.00  smt_fast_solver_calls:                  0
% 1.89/1.00  prop_num_of_clauses:                    856
% 1.89/1.00  prop_preprocess_simplified:             3791
% 1.89/1.00  prop_fo_subsumed:                       24
% 1.89/1.00  prop_solver_time:                       0.
% 1.89/1.00  smt_solver_time:                        0.
% 1.89/1.00  smt_fast_solver_time:                   0.
% 1.89/1.00  prop_fast_solver_time:                  0.
% 1.89/1.00  prop_unsat_core_time:                   0.
% 1.89/1.00  
% 1.89/1.00  ------ QBF
% 1.89/1.00  
% 1.89/1.00  qbf_q_res:                              0
% 1.89/1.00  qbf_num_tautologies:                    0
% 1.89/1.00  qbf_prep_cycles:                        0
% 1.89/1.00  
% 1.89/1.00  ------ BMC1
% 1.89/1.00  
% 1.89/1.00  bmc1_current_bound:                     -1
% 1.89/1.00  bmc1_last_solved_bound:                 -1
% 1.89/1.00  bmc1_unsat_core_size:                   -1
% 1.89/1.00  bmc1_unsat_core_parents_size:           -1
% 1.89/1.00  bmc1_merge_next_fun:                    0
% 1.89/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.89/1.00  
% 1.89/1.00  ------ Instantiation
% 1.89/1.00  
% 1.89/1.00  inst_num_of_clauses:                    274
% 1.89/1.00  inst_num_in_passive:                    29
% 1.89/1.00  inst_num_in_active:                     224
% 1.89/1.00  inst_num_in_unprocessed:                20
% 1.89/1.00  inst_num_of_loops:                      248
% 1.89/1.00  inst_num_of_learning_restarts:          0
% 1.89/1.00  inst_num_moves_active_passive:          18
% 1.89/1.00  inst_lit_activity:                      0
% 1.89/1.00  inst_lit_activity_moves:                0
% 1.89/1.00  inst_num_tautologies:                   0
% 1.89/1.00  inst_num_prop_implied:                  0
% 1.89/1.00  inst_num_existing_simplified:           0
% 1.89/1.00  inst_num_eq_res_simplified:             0
% 1.89/1.00  inst_num_child_elim:                    0
% 1.89/1.00  inst_num_of_dismatching_blockings:      80
% 1.89/1.00  inst_num_of_non_proper_insts:           306
% 1.89/1.00  inst_num_of_duplicates:                 0
% 1.89/1.00  inst_inst_num_from_inst_to_res:         0
% 1.89/1.00  inst_dismatching_checking_time:         0.
% 1.89/1.00  
% 1.89/1.00  ------ Resolution
% 1.89/1.00  
% 1.89/1.00  res_num_of_clauses:                     0
% 1.89/1.00  res_num_in_passive:                     0
% 1.89/1.00  res_num_in_active:                      0
% 1.89/1.00  res_num_of_loops:                       143
% 1.89/1.00  res_forward_subset_subsumed:            69
% 1.89/1.00  res_backward_subset_subsumed:           0
% 1.89/1.00  res_forward_subsumed:                   0
% 1.89/1.00  res_backward_subsumed:                  0
% 1.89/1.00  res_forward_subsumption_resolution:     2
% 1.89/1.00  res_backward_subsumption_resolution:    0
% 1.89/1.00  res_clause_to_clause_subsumption:       211
% 1.89/1.00  res_orphan_elimination:                 0
% 1.89/1.00  res_tautology_del:                      100
% 1.89/1.00  res_num_eq_res_simplified:              0
% 1.89/1.00  res_num_sel_changes:                    0
% 1.89/1.00  res_moves_from_active_to_pass:          0
% 1.89/1.00  
% 1.89/1.00  ------ Superposition
% 1.89/1.00  
% 1.89/1.00  sup_time_total:                         0.
% 1.89/1.00  sup_time_generating:                    0.
% 1.89/1.00  sup_time_sim_full:                      0.
% 1.89/1.00  sup_time_sim_immed:                     0.
% 1.89/1.00  
% 1.89/1.00  sup_num_of_clauses:                     56
% 1.89/1.00  sup_num_in_active:                      48
% 1.89/1.00  sup_num_in_passive:                     8
% 1.89/1.00  sup_num_of_loops:                       48
% 1.89/1.00  sup_fw_superposition:                   30
% 1.89/1.00  sup_bw_superposition:                   12
% 1.89/1.00  sup_immediate_simplified:               9
% 1.89/1.00  sup_given_eliminated:                   0
% 1.89/1.00  comparisons_done:                       0
% 1.89/1.00  comparisons_avoided:                    0
% 1.89/1.00  
% 1.89/1.00  ------ Simplifications
% 1.89/1.00  
% 1.89/1.00  
% 1.89/1.00  sim_fw_subset_subsumed:                 9
% 1.89/1.00  sim_bw_subset_subsumed:                 0
% 1.89/1.00  sim_fw_subsumed:                        0
% 1.89/1.00  sim_bw_subsumed:                        0
% 1.89/1.00  sim_fw_subsumption_res:                 1
% 1.89/1.00  sim_bw_subsumption_res:                 0
% 1.89/1.00  sim_tautology_del:                      2
% 1.89/1.00  sim_eq_tautology_del:                   0
% 1.89/1.00  sim_eq_res_simp:                        0
% 1.89/1.00  sim_fw_demodulated:                     0
% 1.89/1.00  sim_bw_demodulated:                     0
% 1.89/1.00  sim_light_normalised:                   4
% 1.89/1.00  sim_joinable_taut:                      0
% 1.89/1.00  sim_joinable_simp:                      0
% 1.89/1.00  sim_ac_normalised:                      0
% 1.89/1.00  sim_smt_subsumption:                    0
% 1.89/1.00  
%------------------------------------------------------------------------------
