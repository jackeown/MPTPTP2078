%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:21 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  212 (2311 expanded)
%              Number of clauses        :  145 ( 588 expanded)
%              Number of leaves         :   17 ( 923 expanded)
%              Depth                    :   29
%              Number of atoms          : 1184 (36250 expanded)
%              Number of equality atoms :  479 (3157 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
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
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & ! [X6] :
              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
              | ~ r2_hidden(X6,u1_struct_0(X2))
              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & ! [X6] :
            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(sK6,X6)
            | ~ r2_hidden(X6,u1_struct_0(X2))
            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & ! [X6] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                  | ~ r2_hidden(X6,u1_struct_0(X2))
                  | ~ m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK5),X5)
            & ! [X6] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X6) = k1_funct_1(X5,X6)
                | ~ r2_hidden(X6,u1_struct_0(X2))
                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & ! [X6] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                      | ~ r2_hidden(X6,u1_struct_0(X2))
                      | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X4),X5)
                & ! [X6] :
                    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                    | ~ r2_hidden(X6,u1_struct_0(X2))
                    | ~ m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                          | ~ r2_hidden(X6,u1_struct_0(X2))
                          | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X4),X5)
                    & ! [X6] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                        | ~ r2_hidden(X6,u1_struct_0(sK3))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                                | ~ r2_hidden(X6,u1_struct_0(X2))
                                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f28,f36,f35,f34,f33,f32,f31])).

fof(f65,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X6] :
      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) = k1_funct_1(sK6,X6)
      | ~ r2_hidden(X6,u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f37])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_659,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1197,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_655,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1201,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(sK0(X1,X2,X0,X4,X3),X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_662,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(sK0(X1_54,X2_54,X0_54,X4_54,X3_54),X1_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1194,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | m1_subset_1(sK0(X0_54,X1_54,X2_54,X3_54,X4_54),X0_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_665,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ m1_subset_1(X3_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_xboole_0(X1_54)
    | ~ v1_funct_1(X0_54)
    | k3_funct_2(X1_54,X2_54,X0_54,X3_54) = k1_funct_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1191,plain,
    ( k3_funct_2(X0_54,X1_54,X2_54,X3_54) = k1_funct_1(X2_54,X3_54)
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,X0_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_2265,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK5,X0_54)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1191])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_40,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_41,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2432,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2265,c_40,c_41])).

cnf(c_2433,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK5,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2432])).

cnf(c_2600,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),X0_54,X1_54,X2_54,X3_54)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),X0_54,X1_54,X2_54,X3_54))
    | k2_partfun1(u1_struct_0(sK4),X0_54,X1_54,X2_54) = X3_54
    | v1_funct_2(X3_54,X2_54,X0_54) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),X0_54) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X0_54))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_2433])).

cnf(c_3773,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54))
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_2600])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1190,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_2224,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1190])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_2393,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_19,c_17,c_1513])).

cnf(c_3830,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54))
    | k7_relat_1(sK5,X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3773,c_2393])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_35,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_72,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_74,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_76,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_78,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_3849,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | v1_funct_2(X1_54,X0_54,u1_struct_0(sK2)) != iProver_top
    | k7_relat_1(sK5,X0_54) = X1_54
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54))
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_33,c_35,c_40,c_41,c_74,c_78])).

cnf(c_3850,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54,X1_54))
    | k7_relat_1(sK5,X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3849])).

cnf(c_3863,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_3850])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_39,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_44,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_45,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_661,plain,
    ( m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1485,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_1486,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1485])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_667,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1797,plain,
    ( ~ m1_pre_topc(sK4,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1872,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_1873,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1872])).

cnf(c_656,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1200,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_1189,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_2097,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1189])).

cnf(c_313,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_642,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_3743,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_3744,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3743])).

cnf(c_4009,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3863,c_32,c_36,c_39,c_43,c_44,c_45,c_1486,c_1873,c_2097,c_3744])).

cnf(c_1214,plain,
    ( v1_xboole_0(u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_4016,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_1214])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4017,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4016])).

cnf(c_4124,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4016,c_32,c_38,c_39,c_1873])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,sK0(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK0(X1,X2,X0,X4,X3))
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_664,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | k3_funct_2(X1_54,X2_54,X0_54,sK0(X1_54,X2_54,X0_54,X4_54,X3_54)) != k1_funct_1(X3_54,sK0(X1_54,X2_54,X0_54,X4_54,X3_54))
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1192,plain,
    ( k3_funct_2(X0_54,X1_54,X2_54,sK0(X0_54,X1_54,X2_54,X3_54,X4_54)) != k1_funct_1(X4_54,sK0(X0_54,X1_54,X2_54,X3_54,X4_54))
    | k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_4128,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = sK6
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4124,c_1192])).

cnf(c_4129,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4128,c_2393])).

cnf(c_38,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | r2_hidden(sK0(X1,X2,X0,X4,X3),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_663,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | r2_hidden(sK0(X1_54,X2_54,X0_54,X4_54,X3_54),X4_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1193,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | r2_hidden(sK0(X0_54,X1_54,X2_54,X3_54,X4_54),X3_54) = iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_660,negated_conjecture,
    ( ~ r2_hidden(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK6,X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1196,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK6,X0_54)
    | r2_hidden(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_2305,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(X0_54,X1_54,X2_54,u1_struct_0(sK3),X3_54)) = k1_funct_1(sK6,sK0(X0_54,X1_54,X2_54,u1_struct_0(sK3),X3_54))
    | k2_partfun1(X0_54,X1_54,X2_54,u1_struct_0(sK3)) = X3_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X3_54,u1_struct_0(sK3),X1_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1_54))) != iProver_top
    | m1_subset_1(sK0(X0_54,X1_54,X2_54,u1_struct_0(sK3),X3_54),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1196])).

cnf(c_3446,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54))
    | k2_partfun1(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK4),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK3),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_54))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_2305])).

cnf(c_4313,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54))
    | k2_partfun1(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK4),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK3),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3446,c_32,c_36,c_39,c_43,c_1486,c_1873,c_2097,c_3744])).

cnf(c_4314,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3),X2_54))
    | k2_partfun1(u1_struct_0(sK4),X0_54,X1_54,u1_struct_0(sK3)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK4),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK3),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4313])).

cnf(c_4329,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54))
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_4314])).

cnf(c_4380,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4329,c_2393])).

cnf(c_4428,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | k7_relat_1(sK5,u1_struct_0(sK3)) = X0_54
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_33,c_35,c_40,c_41,c_74,c_78])).

cnf(c_4429,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),X0_54))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4428])).

cnf(c_4440,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_4429])).

cnf(c_4540,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4440,c_44,c_45])).

cnf(c_4541,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4540])).

cnf(c_4547,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4541,c_1214])).

cnf(c_4548,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4547])).

cnf(c_4639,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3),sK6))
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4547,c_32,c_38,c_39,c_1873])).

cnf(c_4644,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = sK6
    | k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4639,c_1192])).

cnf(c_4662,plain,
    ( k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4644,c_2393])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_46,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4676,plain,
    ( k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4662,c_32,c_33,c_35,c_36,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_46,c_74,c_78,c_1486,c_1873,c_2097,c_3744])).

cnf(c_4682,plain,
    ( k7_relat_1(sK5,u1_struct_0(sK3)) = sK6
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4676,c_1214])).

cnf(c_4704,plain,
    ( k7_relat_1(sK5,u1_struct_0(sK3)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4129,c_32,c_38,c_39,c_1873,c_4682])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_331,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != X0
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_332,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | sK6 != k3_tmap_1(sK1,sK2,sK4,sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_641,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | sK6 != k3_tmap_1(sK1,sK2,sK4,sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_670,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | sP0_iProver_split
    | sK6 != k3_tmap_1(sK1,sK2,sK4,sK3,sK5) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_641])).

cnf(c_1215,plain,
    ( sK6 != k3_tmap_1(sK1,sK2,sK4,sK3,sK5)
    | v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_641])).

cnf(c_1216,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_1306,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != sK6
    | v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1215,c_1216])).

cnf(c_652,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1204,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_668,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1188,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1863,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1188])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_34,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2892,plain,
    ( v2_pre_topc(X1_55) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1863,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2893,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK2,sK4,X0_55,sK5)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2892])).

cnf(c_2898,plain,
    ( k3_tmap_1(X0_55,sK2,sK4,X1_55,sK5) = k7_relat_1(sK5,u1_struct_0(X1_55))
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2893,c_2393])).

cnf(c_2909,plain,
    ( k3_tmap_1(sK1,sK2,sK4,X0_55,sK5) = k7_relat_1(sK5,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(X0_55,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_2898])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3175,plain,
    ( m1_pre_topc(X0_55,sK1) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | k3_tmap_1(sK1,sK2,sK4,X0_55,sK5) = k7_relat_1(sK5,u1_struct_0(X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2909,c_30,c_31,c_32])).

cnf(c_3176,plain,
    ( k3_tmap_1(sK1,sK2,sK4,X0_55,sK5) = k7_relat_1(sK5,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(X0_55,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3175])).

cnf(c_3184,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3))
    | m1_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_3176])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3187,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3184,c_37])).

cnf(c_3451,plain,
    ( k7_relat_1(sK5,u1_struct_0(sK3)) != sK6
    | v1_funct_2(k7_relat_1(sK5,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1306,c_3187])).

cnf(c_4708,plain,
    ( sK6 != sK6
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4704,c_3451])).

cnf(c_4712,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4708])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4712,c_46,c_45,c_44])).


%------------------------------------------------------------------------------
