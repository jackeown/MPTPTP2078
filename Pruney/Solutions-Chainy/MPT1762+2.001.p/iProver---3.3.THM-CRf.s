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
% DateTime   : Thu Dec  3 12:22:50 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  238 (4328 expanded)
%              Number of clauses        :  151 ( 947 expanded)
%              Number of leaves         :   22 (1844 expanded)
%              Depth                    :   24
%              Number of atoms          : 1252 (75000 expanded)
%              Number of equality atoms :  299 (5556 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
                                   => k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
                                     => k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & ! [X6] :
              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
              | ~ r2_hidden(X6,u1_struct_0(X2))
              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & ! [X6] :
            ( k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            | ~ r2_hidden(X6,u1_struct_0(X2))
            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & ! [X6] :
                  ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
                ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X6)
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & ! [X6] :
                      ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
                    ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X6)
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

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
                        ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
                            ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X6)
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

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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
                              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6)
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

fof(f57,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)
    & ! [X6] :
        ( k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f56,f55,f54,f53,f52,f51])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
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
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f41])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X6] :
      ( k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6)
      | ~ r2_hidden(X6,u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1248,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1960,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1253,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1955,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1264,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | v2_struct_0(X3_56)
    | v2_struct_0(X1_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | ~ v2_pre_topc(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1944,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)
    | v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_4089,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X0_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1944])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1940,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_3666,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1940])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2380,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_4016,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3666,c_28,c_26,c_2380])).

cnf(c_4102,plain,
    ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4089,c_4016])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6598,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4102,c_42,c_43,c_44,c_49,c_50])).

cnf(c_6599,plain,
    ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_6598])).

cnf(c_6613,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3))
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_6599])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_52,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7085,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6613,c_39,c_40,c_41,c_48,c_52])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_711,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != X3
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_712,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | ~ v1_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_714,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_24,c_23,c_22])).

cnf(c_715,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_1237,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_715])).

cnf(c_1971,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_716,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1261,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | v2_struct_0(X3_56)
    | v2_struct_0(X1_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | ~ v2_pre_topc(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2415,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(sK4,X1_56)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_2535,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_56,sK1)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_2650,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_2651,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2650])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1262,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k3_tmap_1(X2_56,X1_56,X0_56,X3_56,X0_55),u1_struct_0(X3_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | v2_struct_0(X2_56)
    | v2_struct_0(X1_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | ~ v2_pre_topc(X2_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2431,plain,
    ( v1_funct_2(k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5),u1_struct_0(X1_56),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ m1_pre_topc(sK4,X0_56)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_2564,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5),u1_struct_0(X0_56),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_56,sK1)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2431])).

cnf(c_2696,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2564])).

cnf(c_2697,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2696])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1263,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | v2_struct_0(X3_56)
    | v2_struct_0(X1_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | ~ v2_pre_topc(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2441,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(sK4,X1_56)
    | m1_subset_1(k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_2583,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_56,sK1)
    | ~ m1_pre_topc(sK4,sK1)
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_2713,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_2714,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2713])).

cnf(c_2803,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_48,c_49,c_50,c_51,c_716,c_2651,c_2697,c_2714])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1935,plain,
    ( m1_subset_1(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,X1_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_2808,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2803,c_1935])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1254,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1954,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1265,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1943,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_3085,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1943])).

cnf(c_1250,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1958,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_3086,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_1943])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_412,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_1240,plain,
    ( v2_struct_0(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_3311,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_3312,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3311])).

cnf(c_5209,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2808,c_41,c_45,c_3085,c_3086,c_3312])).

cnf(c_7091,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7085,c_5209])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1260,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1948,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56))) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1272,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1936,plain,
    ( m1_subset_1(X0_55,X1_55) = iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X1_55)) != iProver_top
    | r2_hidden(X0_55,X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_3496,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_56)) = iProver_top
    | r2_hidden(X0_55,u1_struct_0(X0_56)) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_1948,c_1936])).

cnf(c_7188,plain,
    ( m1_pre_topc(sK3,X0_56) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(X0_56)) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_7091,c_3496])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1267,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ m1_subset_1(X3_55,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | v1_xboole_0(X1_55)
    | k3_funct_2(X1_55,X2_55,X0_55,X3_55) = k1_funct_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1941,plain,
    ( k3_funct_2(X0_55,X1_55,X2_55,X3_55) = k1_funct_1(X2_55,X3_55)
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X3_55,X0_55) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_3689,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1941])).

cnf(c_4850,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3689,c_49,c_50])).

cnf(c_4851,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4850])).

cnf(c_26123,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
    | m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_4851])).

cnf(c_26736,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26123,c_41,c_52,c_3086])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(sK6,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1258,negated_conjecture,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ r2_hidden(X0_55,u1_struct_0(sK3))
    | k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1950,plain,
    ( k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_26124,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_1950])).

cnf(c_26732,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26124,c_41,c_52,c_3086,c_7091])).

cnf(c_26740,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26736,c_26732])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1939,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_2922,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_1939])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1270,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | ~ v1_relat_1(X2_55)
    | ~ v1_funct_1(X2_55)
    | k1_funct_1(k7_relat_1(X2_55,X1_55),X0_55) = k1_funct_1(X2_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1938,plain,
    ( k1_funct_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_funct_1(X0_55,X2_55)
    | r2_hidden(X2_55,X1_55) != iProver_top
    | v1_relat_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_5214,plain,
    ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(X0_55,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
    | v1_relat_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_5209,c_1938])).

cnf(c_6081,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2922,c_5214])).

cnf(c_2338,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2339,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_5216,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5214])).

cnf(c_6369,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6081,c_49,c_51,c_2339,c_5216])).

cnf(c_7089,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
    inference(demodulation,[status(thm)],[c_7085,c_6369])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != X3
    | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK3) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_732,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | ~ v1_funct_1(sK6)
    | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_734,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_24,c_23,c_22])).

cnf(c_735,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_1236,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
    | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(subtyping,[status(esa)],[c_735])).

cnf(c_1972,plain,
    ( k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
    | v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_2855,plain,
    ( k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1972,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_29,c_28,c_27,c_26,c_1236,c_2650,c_2696,c_2713])).

cnf(c_7093,plain,
    ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
    inference(demodulation,[status(thm)],[c_7085,c_2855])).

cnf(c_7110,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
    inference(demodulation,[status(thm)],[c_7089,c_7093])).

cnf(c_26743,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_26740,c_7110])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X2_55,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1937,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | r2_hidden(X2_55,X0_55) != iProver_top
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_3494,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(X0_56)) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_56)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1948,c_1937])).

cnf(c_5482,plain,
    ( m1_pre_topc(sK3,X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_56)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5209,c_3494])).

cnf(c_26745,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_26743,c_5482])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26745,c_3086,c_52,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.79/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/1.52  
% 7.79/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.52  
% 7.79/1.52  ------  iProver source info
% 7.79/1.52  
% 7.79/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.52  git: non_committed_changes: false
% 7.79/1.52  git: last_make_outside_of_git: false
% 7.79/1.52  
% 7.79/1.52  ------ 
% 7.79/1.52  
% 7.79/1.52  ------ Input Options
% 7.79/1.52  
% 7.79/1.52  --out_options                           all
% 7.79/1.52  --tptp_safe_out                         true
% 7.79/1.52  --problem_path                          ""
% 7.79/1.52  --include_path                          ""
% 7.79/1.52  --clausifier                            res/vclausify_rel
% 7.79/1.52  --clausifier_options                    --mode clausify
% 7.79/1.52  --stdin                                 false
% 7.79/1.52  --stats_out                             all
% 7.79/1.52  
% 7.79/1.52  ------ General Options
% 7.79/1.52  
% 7.79/1.52  --fof                                   false
% 7.79/1.52  --time_out_real                         305.
% 7.79/1.52  --time_out_virtual                      -1.
% 7.79/1.52  --symbol_type_check                     false
% 7.79/1.52  --clausify_out                          false
% 7.79/1.52  --sig_cnt_out                           false
% 7.79/1.52  --trig_cnt_out                          false
% 7.79/1.52  --trig_cnt_out_tolerance                1.
% 7.79/1.52  --trig_cnt_out_sk_spl                   false
% 7.79/1.52  --abstr_cl_out                          false
% 7.79/1.52  
% 7.79/1.52  ------ Global Options
% 7.79/1.52  
% 7.79/1.52  --schedule                              default
% 7.79/1.52  --add_important_lit                     false
% 7.79/1.52  --prop_solver_per_cl                    1000
% 7.79/1.52  --min_unsat_core                        false
% 7.79/1.52  --soft_assumptions                      false
% 7.79/1.52  --soft_lemma_size                       3
% 7.79/1.52  --prop_impl_unit_size                   0
% 7.79/1.52  --prop_impl_unit                        []
% 7.79/1.52  --share_sel_clauses                     true
% 7.79/1.52  --reset_solvers                         false
% 7.79/1.52  --bc_imp_inh                            [conj_cone]
% 7.79/1.52  --conj_cone_tolerance                   3.
% 7.79/1.52  --extra_neg_conj                        none
% 7.79/1.52  --large_theory_mode                     true
% 7.79/1.52  --prolific_symb_bound                   200
% 7.79/1.52  --lt_threshold                          2000
% 7.79/1.52  --clause_weak_htbl                      true
% 7.79/1.52  --gc_record_bc_elim                     false
% 7.79/1.52  
% 7.79/1.52  ------ Preprocessing Options
% 7.79/1.52  
% 7.79/1.52  --preprocessing_flag                    true
% 7.79/1.52  --time_out_prep_mult                    0.1
% 7.79/1.52  --splitting_mode                        input
% 7.79/1.52  --splitting_grd                         true
% 7.79/1.52  --splitting_cvd                         false
% 7.79/1.52  --splitting_cvd_svl                     false
% 7.79/1.52  --splitting_nvd                         32
% 7.79/1.52  --sub_typing                            true
% 7.79/1.52  --prep_gs_sim                           true
% 7.79/1.52  --prep_unflatten                        true
% 7.79/1.52  --prep_res_sim                          true
% 7.79/1.52  --prep_upred                            true
% 7.79/1.52  --prep_sem_filter                       exhaustive
% 7.79/1.52  --prep_sem_filter_out                   false
% 7.79/1.52  --pred_elim                             true
% 7.79/1.52  --res_sim_input                         true
% 7.79/1.52  --eq_ax_congr_red                       true
% 7.79/1.52  --pure_diseq_elim                       true
% 7.79/1.52  --brand_transform                       false
% 7.79/1.52  --non_eq_to_eq                          false
% 7.79/1.52  --prep_def_merge                        true
% 7.79/1.52  --prep_def_merge_prop_impl              false
% 7.79/1.52  --prep_def_merge_mbd                    true
% 7.79/1.52  --prep_def_merge_tr_red                 false
% 7.79/1.52  --prep_def_merge_tr_cl                  false
% 7.79/1.52  --smt_preprocessing                     true
% 7.79/1.52  --smt_ac_axioms                         fast
% 7.79/1.52  --preprocessed_out                      false
% 7.79/1.52  --preprocessed_stats                    false
% 7.79/1.52  
% 7.79/1.52  ------ Abstraction refinement Options
% 7.79/1.52  
% 7.79/1.52  --abstr_ref                             []
% 7.79/1.52  --abstr_ref_prep                        false
% 7.79/1.52  --abstr_ref_until_sat                   false
% 7.79/1.52  --abstr_ref_sig_restrict                funpre
% 7.79/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.52  --abstr_ref_under                       []
% 7.79/1.52  
% 7.79/1.52  ------ SAT Options
% 7.79/1.52  
% 7.79/1.52  --sat_mode                              false
% 7.79/1.52  --sat_fm_restart_options                ""
% 7.79/1.52  --sat_gr_def                            false
% 7.79/1.52  --sat_epr_types                         true
% 7.79/1.52  --sat_non_cyclic_types                  false
% 7.79/1.52  --sat_finite_models                     false
% 7.79/1.52  --sat_fm_lemmas                         false
% 7.79/1.52  --sat_fm_prep                           false
% 7.79/1.52  --sat_fm_uc_incr                        true
% 7.79/1.52  --sat_out_model                         small
% 7.79/1.52  --sat_out_clauses                       false
% 7.79/1.52  
% 7.79/1.52  ------ QBF Options
% 7.79/1.52  
% 7.79/1.52  --qbf_mode                              false
% 7.79/1.52  --qbf_elim_univ                         false
% 7.79/1.52  --qbf_dom_inst                          none
% 7.79/1.52  --qbf_dom_pre_inst                      false
% 7.79/1.52  --qbf_sk_in                             false
% 7.79/1.52  --qbf_pred_elim                         true
% 7.79/1.52  --qbf_split                             512
% 7.79/1.52  
% 7.79/1.52  ------ BMC1 Options
% 7.79/1.52  
% 7.79/1.52  --bmc1_incremental                      false
% 7.79/1.52  --bmc1_axioms                           reachable_all
% 7.79/1.52  --bmc1_min_bound                        0
% 7.79/1.52  --bmc1_max_bound                        -1
% 7.79/1.52  --bmc1_max_bound_default                -1
% 7.79/1.52  --bmc1_symbol_reachability              true
% 7.79/1.52  --bmc1_property_lemmas                  false
% 7.79/1.52  --bmc1_k_induction                      false
% 7.79/1.52  --bmc1_non_equiv_states                 false
% 7.79/1.52  --bmc1_deadlock                         false
% 7.79/1.52  --bmc1_ucm                              false
% 7.79/1.52  --bmc1_add_unsat_core                   none
% 7.79/1.53  --bmc1_unsat_core_children              false
% 7.79/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.53  --bmc1_out_stat                         full
% 7.79/1.53  --bmc1_ground_init                      false
% 7.79/1.53  --bmc1_pre_inst_next_state              false
% 7.79/1.53  --bmc1_pre_inst_state                   false
% 7.79/1.53  --bmc1_pre_inst_reach_state             false
% 7.79/1.53  --bmc1_out_unsat_core                   false
% 7.79/1.53  --bmc1_aig_witness_out                  false
% 7.79/1.53  --bmc1_verbose                          false
% 7.79/1.53  --bmc1_dump_clauses_tptp                false
% 7.79/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.53  --bmc1_dump_file                        -
% 7.79/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.53  --bmc1_ucm_extend_mode                  1
% 7.79/1.53  --bmc1_ucm_init_mode                    2
% 7.79/1.53  --bmc1_ucm_cone_mode                    none
% 7.79/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.53  --bmc1_ucm_relax_model                  4
% 7.79/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.53  --bmc1_ucm_layered_model                none
% 7.79/1.53  --bmc1_ucm_max_lemma_size               10
% 7.79/1.53  
% 7.79/1.53  ------ AIG Options
% 7.79/1.53  
% 7.79/1.53  --aig_mode                              false
% 7.79/1.53  
% 7.79/1.53  ------ Instantiation Options
% 7.79/1.53  
% 7.79/1.53  --instantiation_flag                    true
% 7.79/1.53  --inst_sos_flag                         false
% 7.79/1.53  --inst_sos_phase                        true
% 7.79/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.53  --inst_lit_sel_side                     num_symb
% 7.79/1.53  --inst_solver_per_active                1400
% 7.79/1.53  --inst_solver_calls_frac                1.
% 7.79/1.53  --inst_passive_queue_type               priority_queues
% 7.79/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.53  --inst_passive_queues_freq              [25;2]
% 7.79/1.53  --inst_dismatching                      true
% 7.79/1.53  --inst_eager_unprocessed_to_passive     true
% 7.79/1.53  --inst_prop_sim_given                   true
% 7.79/1.53  --inst_prop_sim_new                     false
% 7.79/1.53  --inst_subs_new                         false
% 7.79/1.53  --inst_eq_res_simp                      false
% 7.79/1.53  --inst_subs_given                       false
% 7.79/1.53  --inst_orphan_elimination               true
% 7.79/1.53  --inst_learning_loop_flag               true
% 7.79/1.53  --inst_learning_start                   3000
% 7.79/1.53  --inst_learning_factor                  2
% 7.79/1.53  --inst_start_prop_sim_after_learn       3
% 7.79/1.53  --inst_sel_renew                        solver
% 7.79/1.53  --inst_lit_activity_flag                true
% 7.79/1.53  --inst_restr_to_given                   false
% 7.79/1.53  --inst_activity_threshold               500
% 7.79/1.53  --inst_out_proof                        true
% 7.79/1.53  
% 7.79/1.53  ------ Resolution Options
% 7.79/1.53  
% 7.79/1.53  --resolution_flag                       true
% 7.79/1.53  --res_lit_sel                           adaptive
% 7.79/1.53  --res_lit_sel_side                      none
% 7.79/1.53  --res_ordering                          kbo
% 7.79/1.53  --res_to_prop_solver                    active
% 7.79/1.53  --res_prop_simpl_new                    false
% 7.79/1.53  --res_prop_simpl_given                  true
% 7.79/1.53  --res_passive_queue_type                priority_queues
% 7.79/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.53  --res_passive_queues_freq               [15;5]
% 7.79/1.53  --res_forward_subs                      full
% 7.79/1.53  --res_backward_subs                     full
% 7.79/1.53  --res_forward_subs_resolution           true
% 7.79/1.53  --res_backward_subs_resolution          true
% 7.79/1.53  --res_orphan_elimination                true
% 7.79/1.53  --res_time_limit                        2.
% 7.79/1.53  --res_out_proof                         true
% 7.79/1.53  
% 7.79/1.53  ------ Superposition Options
% 7.79/1.53  
% 7.79/1.53  --superposition_flag                    true
% 7.79/1.53  --sup_passive_queue_type                priority_queues
% 7.79/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.53  --demod_completeness_check              fast
% 7.79/1.53  --demod_use_ground                      true
% 7.79/1.53  --sup_to_prop_solver                    passive
% 7.79/1.53  --sup_prop_simpl_new                    true
% 7.79/1.53  --sup_prop_simpl_given                  true
% 7.79/1.53  --sup_fun_splitting                     false
% 7.79/1.53  --sup_smt_interval                      50000
% 7.79/1.53  
% 7.79/1.53  ------ Superposition Simplification Setup
% 7.79/1.53  
% 7.79/1.53  --sup_indices_passive                   []
% 7.79/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_full_bw                           [BwDemod]
% 7.79/1.53  --sup_immed_triv                        [TrivRules]
% 7.79/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_immed_bw_main                     []
% 7.79/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.53  
% 7.79/1.53  ------ Combination Options
% 7.79/1.53  
% 7.79/1.53  --comb_res_mult                         3
% 7.79/1.53  --comb_sup_mult                         2
% 7.79/1.53  --comb_inst_mult                        10
% 7.79/1.53  
% 7.79/1.53  ------ Debug Options
% 7.79/1.53  
% 7.79/1.53  --dbg_backtrace                         false
% 7.79/1.53  --dbg_dump_prop_clauses                 false
% 7.79/1.53  --dbg_dump_prop_clauses_file            -
% 7.79/1.53  --dbg_out_stat                          false
% 7.79/1.53  ------ Parsing...
% 7.79/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.53  
% 7.79/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.79/1.53  
% 7.79/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.53  
% 7.79/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.53  ------ Proving...
% 7.79/1.53  ------ Problem Properties 
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  clauses                                 38
% 7.79/1.53  conjectures                             18
% 7.79/1.53  EPR                                     17
% 7.79/1.53  Horn                                    31
% 7.79/1.53  unary                                   17
% 7.79/1.53  binary                                  2
% 7.79/1.53  lits                                    134
% 7.79/1.53  lits eq                                 9
% 7.79/1.53  fd_pure                                 0
% 7.79/1.53  fd_pseudo                               0
% 7.79/1.53  fd_cond                                 0
% 7.79/1.53  fd_pseudo_cond                          0
% 7.79/1.53  AC symbols                              0
% 7.79/1.53  
% 7.79/1.53  ------ Schedule dynamic 5 is on 
% 7.79/1.53  
% 7.79/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  ------ 
% 7.79/1.53  Current options:
% 7.79/1.53  ------ 
% 7.79/1.53  
% 7.79/1.53  ------ Input Options
% 7.79/1.53  
% 7.79/1.53  --out_options                           all
% 7.79/1.53  --tptp_safe_out                         true
% 7.79/1.53  --problem_path                          ""
% 7.79/1.53  --include_path                          ""
% 7.79/1.53  --clausifier                            res/vclausify_rel
% 7.79/1.53  --clausifier_options                    --mode clausify
% 7.79/1.53  --stdin                                 false
% 7.79/1.53  --stats_out                             all
% 7.79/1.53  
% 7.79/1.53  ------ General Options
% 7.79/1.53  
% 7.79/1.53  --fof                                   false
% 7.79/1.53  --time_out_real                         305.
% 7.79/1.53  --time_out_virtual                      -1.
% 7.79/1.53  --symbol_type_check                     false
% 7.79/1.53  --clausify_out                          false
% 7.79/1.53  --sig_cnt_out                           false
% 7.79/1.53  --trig_cnt_out                          false
% 7.79/1.53  --trig_cnt_out_tolerance                1.
% 7.79/1.53  --trig_cnt_out_sk_spl                   false
% 7.79/1.53  --abstr_cl_out                          false
% 7.79/1.53  
% 7.79/1.53  ------ Global Options
% 7.79/1.53  
% 7.79/1.53  --schedule                              default
% 7.79/1.53  --add_important_lit                     false
% 7.79/1.53  --prop_solver_per_cl                    1000
% 7.79/1.53  --min_unsat_core                        false
% 7.79/1.53  --soft_assumptions                      false
% 7.79/1.53  --soft_lemma_size                       3
% 7.79/1.53  --prop_impl_unit_size                   0
% 7.79/1.53  --prop_impl_unit                        []
% 7.79/1.53  --share_sel_clauses                     true
% 7.79/1.53  --reset_solvers                         false
% 7.79/1.53  --bc_imp_inh                            [conj_cone]
% 7.79/1.53  --conj_cone_tolerance                   3.
% 7.79/1.53  --extra_neg_conj                        none
% 7.79/1.53  --large_theory_mode                     true
% 7.79/1.53  --prolific_symb_bound                   200
% 7.79/1.53  --lt_threshold                          2000
% 7.79/1.53  --clause_weak_htbl                      true
% 7.79/1.53  --gc_record_bc_elim                     false
% 7.79/1.53  
% 7.79/1.53  ------ Preprocessing Options
% 7.79/1.53  
% 7.79/1.53  --preprocessing_flag                    true
% 7.79/1.53  --time_out_prep_mult                    0.1
% 7.79/1.53  --splitting_mode                        input
% 7.79/1.53  --splitting_grd                         true
% 7.79/1.53  --splitting_cvd                         false
% 7.79/1.53  --splitting_cvd_svl                     false
% 7.79/1.53  --splitting_nvd                         32
% 7.79/1.53  --sub_typing                            true
% 7.79/1.53  --prep_gs_sim                           true
% 7.79/1.53  --prep_unflatten                        true
% 7.79/1.53  --prep_res_sim                          true
% 7.79/1.53  --prep_upred                            true
% 7.79/1.53  --prep_sem_filter                       exhaustive
% 7.79/1.53  --prep_sem_filter_out                   false
% 7.79/1.53  --pred_elim                             true
% 7.79/1.53  --res_sim_input                         true
% 7.79/1.53  --eq_ax_congr_red                       true
% 7.79/1.53  --pure_diseq_elim                       true
% 7.79/1.53  --brand_transform                       false
% 7.79/1.53  --non_eq_to_eq                          false
% 7.79/1.53  --prep_def_merge                        true
% 7.79/1.53  --prep_def_merge_prop_impl              false
% 7.79/1.53  --prep_def_merge_mbd                    true
% 7.79/1.53  --prep_def_merge_tr_red                 false
% 7.79/1.53  --prep_def_merge_tr_cl                  false
% 7.79/1.53  --smt_preprocessing                     true
% 7.79/1.53  --smt_ac_axioms                         fast
% 7.79/1.53  --preprocessed_out                      false
% 7.79/1.53  --preprocessed_stats                    false
% 7.79/1.53  
% 7.79/1.53  ------ Abstraction refinement Options
% 7.79/1.53  
% 7.79/1.53  --abstr_ref                             []
% 7.79/1.53  --abstr_ref_prep                        false
% 7.79/1.53  --abstr_ref_until_sat                   false
% 7.79/1.53  --abstr_ref_sig_restrict                funpre
% 7.79/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.53  --abstr_ref_under                       []
% 7.79/1.53  
% 7.79/1.53  ------ SAT Options
% 7.79/1.53  
% 7.79/1.53  --sat_mode                              false
% 7.79/1.53  --sat_fm_restart_options                ""
% 7.79/1.53  --sat_gr_def                            false
% 7.79/1.53  --sat_epr_types                         true
% 7.79/1.53  --sat_non_cyclic_types                  false
% 7.79/1.53  --sat_finite_models                     false
% 7.79/1.53  --sat_fm_lemmas                         false
% 7.79/1.53  --sat_fm_prep                           false
% 7.79/1.53  --sat_fm_uc_incr                        true
% 7.79/1.53  --sat_out_model                         small
% 7.79/1.53  --sat_out_clauses                       false
% 7.79/1.53  
% 7.79/1.53  ------ QBF Options
% 7.79/1.53  
% 7.79/1.53  --qbf_mode                              false
% 7.79/1.53  --qbf_elim_univ                         false
% 7.79/1.53  --qbf_dom_inst                          none
% 7.79/1.53  --qbf_dom_pre_inst                      false
% 7.79/1.53  --qbf_sk_in                             false
% 7.79/1.53  --qbf_pred_elim                         true
% 7.79/1.53  --qbf_split                             512
% 7.79/1.53  
% 7.79/1.53  ------ BMC1 Options
% 7.79/1.53  
% 7.79/1.53  --bmc1_incremental                      false
% 7.79/1.53  --bmc1_axioms                           reachable_all
% 7.79/1.53  --bmc1_min_bound                        0
% 7.79/1.53  --bmc1_max_bound                        -1
% 7.79/1.53  --bmc1_max_bound_default                -1
% 7.79/1.53  --bmc1_symbol_reachability              true
% 7.79/1.53  --bmc1_property_lemmas                  false
% 7.79/1.53  --bmc1_k_induction                      false
% 7.79/1.53  --bmc1_non_equiv_states                 false
% 7.79/1.53  --bmc1_deadlock                         false
% 7.79/1.53  --bmc1_ucm                              false
% 7.79/1.53  --bmc1_add_unsat_core                   none
% 7.79/1.53  --bmc1_unsat_core_children              false
% 7.79/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.53  --bmc1_out_stat                         full
% 7.79/1.53  --bmc1_ground_init                      false
% 7.79/1.53  --bmc1_pre_inst_next_state              false
% 7.79/1.53  --bmc1_pre_inst_state                   false
% 7.79/1.53  --bmc1_pre_inst_reach_state             false
% 7.79/1.53  --bmc1_out_unsat_core                   false
% 7.79/1.53  --bmc1_aig_witness_out                  false
% 7.79/1.53  --bmc1_verbose                          false
% 7.79/1.53  --bmc1_dump_clauses_tptp                false
% 7.79/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.53  --bmc1_dump_file                        -
% 7.79/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.53  --bmc1_ucm_extend_mode                  1
% 7.79/1.53  --bmc1_ucm_init_mode                    2
% 7.79/1.53  --bmc1_ucm_cone_mode                    none
% 7.79/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.53  --bmc1_ucm_relax_model                  4
% 7.79/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.53  --bmc1_ucm_layered_model                none
% 7.79/1.53  --bmc1_ucm_max_lemma_size               10
% 7.79/1.53  
% 7.79/1.53  ------ AIG Options
% 7.79/1.53  
% 7.79/1.53  --aig_mode                              false
% 7.79/1.53  
% 7.79/1.53  ------ Instantiation Options
% 7.79/1.53  
% 7.79/1.53  --instantiation_flag                    true
% 7.79/1.53  --inst_sos_flag                         false
% 7.79/1.53  --inst_sos_phase                        true
% 7.79/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.53  --inst_lit_sel_side                     none
% 7.79/1.53  --inst_solver_per_active                1400
% 7.79/1.53  --inst_solver_calls_frac                1.
% 7.79/1.53  --inst_passive_queue_type               priority_queues
% 7.79/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.53  --inst_passive_queues_freq              [25;2]
% 7.79/1.53  --inst_dismatching                      true
% 7.79/1.53  --inst_eager_unprocessed_to_passive     true
% 7.79/1.53  --inst_prop_sim_given                   true
% 7.79/1.53  --inst_prop_sim_new                     false
% 7.79/1.53  --inst_subs_new                         false
% 7.79/1.53  --inst_eq_res_simp                      false
% 7.79/1.53  --inst_subs_given                       false
% 7.79/1.53  --inst_orphan_elimination               true
% 7.79/1.53  --inst_learning_loop_flag               true
% 7.79/1.53  --inst_learning_start                   3000
% 7.79/1.53  --inst_learning_factor                  2
% 7.79/1.53  --inst_start_prop_sim_after_learn       3
% 7.79/1.53  --inst_sel_renew                        solver
% 7.79/1.53  --inst_lit_activity_flag                true
% 7.79/1.53  --inst_restr_to_given                   false
% 7.79/1.53  --inst_activity_threshold               500
% 7.79/1.53  --inst_out_proof                        true
% 7.79/1.53  
% 7.79/1.53  ------ Resolution Options
% 7.79/1.53  
% 7.79/1.53  --resolution_flag                       false
% 7.79/1.53  --res_lit_sel                           adaptive
% 7.79/1.53  --res_lit_sel_side                      none
% 7.79/1.53  --res_ordering                          kbo
% 7.79/1.53  --res_to_prop_solver                    active
% 7.79/1.53  --res_prop_simpl_new                    false
% 7.79/1.53  --res_prop_simpl_given                  true
% 7.79/1.53  --res_passive_queue_type                priority_queues
% 7.79/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.53  --res_passive_queues_freq               [15;5]
% 7.79/1.53  --res_forward_subs                      full
% 7.79/1.53  --res_backward_subs                     full
% 7.79/1.53  --res_forward_subs_resolution           true
% 7.79/1.53  --res_backward_subs_resolution          true
% 7.79/1.53  --res_orphan_elimination                true
% 7.79/1.53  --res_time_limit                        2.
% 7.79/1.53  --res_out_proof                         true
% 7.79/1.53  
% 7.79/1.53  ------ Superposition Options
% 7.79/1.53  
% 7.79/1.53  --superposition_flag                    true
% 7.79/1.53  --sup_passive_queue_type                priority_queues
% 7.79/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.53  --demod_completeness_check              fast
% 7.79/1.53  --demod_use_ground                      true
% 7.79/1.53  --sup_to_prop_solver                    passive
% 7.79/1.53  --sup_prop_simpl_new                    true
% 7.79/1.53  --sup_prop_simpl_given                  true
% 7.79/1.53  --sup_fun_splitting                     false
% 7.79/1.53  --sup_smt_interval                      50000
% 7.79/1.53  
% 7.79/1.53  ------ Superposition Simplification Setup
% 7.79/1.53  
% 7.79/1.53  --sup_indices_passive                   []
% 7.79/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_full_bw                           [BwDemod]
% 7.79/1.53  --sup_immed_triv                        [TrivRules]
% 7.79/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_immed_bw_main                     []
% 7.79/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.53  
% 7.79/1.53  ------ Combination Options
% 7.79/1.53  
% 7.79/1.53  --comb_res_mult                         3
% 7.79/1.53  --comb_sup_mult                         2
% 7.79/1.53  --comb_inst_mult                        10
% 7.79/1.53  
% 7.79/1.53  ------ Debug Options
% 7.79/1.53  
% 7.79/1.53  --dbg_backtrace                         false
% 7.79/1.53  --dbg_dump_prop_clauses                 false
% 7.79/1.53  --dbg_dump_prop_clauses_file            -
% 7.79/1.53  --dbg_out_stat                          false
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  ------ Proving...
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  % SZS status Theorem for theBenchmark.p
% 7.79/1.53  
% 7.79/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.53  
% 7.79/1.53  fof(f17,conjecture,(
% 7.79/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f18,negated_conjecture,(
% 7.79/1.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 7.79/1.53    inference(negated_conjecture,[],[f17])).
% 7.79/1.53  
% 7.79/1.53  fof(f45,plain,(
% 7.79/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : ((k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.79/1.53    inference(ennf_transformation,[],[f18])).
% 7.79/1.53  
% 7.79/1.53  fof(f46,plain,(
% 7.79/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.53    inference(flattening,[],[f45])).
% 7.79/1.53  
% 7.79/1.53  fof(f56,plain,(
% 7.79/1.53    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK6) & ! [X6] : (k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f55,plain,(
% 7.79/1.53    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK5),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f54,plain,(
% 7.79/1.53    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f53,plain,(
% 7.79/1.53    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f52,plain,(
% 7.79/1.53    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f51,plain,(
% 7.79/1.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f57,plain,(
% 7.79/1.53    (((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) & ! [X6] : (k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.79/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f56,f55,f54,f53,f52,f51])).
% 7.79/1.53  
% 7.79/1.53  fof(f85,plain,(
% 7.79/1.53    m1_pre_topc(sK3,sK1)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f90,plain,(
% 7.79/1.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f13,axiom,(
% 7.79/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f39,plain,(
% 7.79/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.79/1.53    inference(ennf_transformation,[],[f13])).
% 7.79/1.53  
% 7.79/1.53  fof(f40,plain,(
% 7.79/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.53    inference(flattening,[],[f39])).
% 7.79/1.53  
% 7.79/1.53  fof(f72,plain,(
% 7.79/1.53    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f40])).
% 7.79/1.53  
% 7.79/1.53  fof(f7,axiom,(
% 7.79/1.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f29,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.79/1.53    inference(ennf_transformation,[],[f7])).
% 7.79/1.53  
% 7.79/1.53  fof(f30,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.79/1.53    inference(flattening,[],[f29])).
% 7.79/1.53  
% 7.79/1.53  fof(f66,plain,(
% 7.79/1.53    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f30])).
% 7.79/1.53  
% 7.79/1.53  fof(f88,plain,(
% 7.79/1.53    v1_funct_1(sK5)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f81,plain,(
% 7.79/1.53    ~v2_struct_0(sK2)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f82,plain,(
% 7.79/1.53    v2_pre_topc(sK2)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f83,plain,(
% 7.79/1.53    l1_pre_topc(sK2)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f89,plain,(
% 7.79/1.53    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f78,plain,(
% 7.79/1.53    ~v2_struct_0(sK1)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f79,plain,(
% 7.79/1.53    v2_pre_topc(sK1)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f80,plain,(
% 7.79/1.53    l1_pre_topc(sK1)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f87,plain,(
% 7.79/1.53    m1_pre_topc(sK4,sK1)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f91,plain,(
% 7.79/1.53    m1_pre_topc(sK3,sK4)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f6,axiom,(
% 7.79/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f27,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.79/1.53    inference(ennf_transformation,[],[f6])).
% 7.79/1.53  
% 7.79/1.53  fof(f28,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.53    inference(flattening,[],[f27])).
% 7.79/1.53  
% 7.79/1.53  fof(f47,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.53    inference(nnf_transformation,[],[f28])).
% 7.79/1.53  
% 7.79/1.53  fof(f48,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.53    inference(rectify,[],[f47])).
% 7.79/1.53  
% 7.79/1.53  fof(f49,plain,(
% 7.79/1.53    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 7.79/1.53    introduced(choice_axiom,[])).
% 7.79/1.53  
% 7.79/1.53  fof(f50,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 7.79/1.53  
% 7.79/1.53  fof(f64,plain,(
% 7.79/1.53    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f50])).
% 7.79/1.53  
% 7.79/1.53  fof(f96,plain,(
% 7.79/1.53    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f92,plain,(
% 7.79/1.53    v1_funct_1(sK6)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f93,plain,(
% 7.79/1.53    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f94,plain,(
% 7.79/1.53    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f14,axiom,(
% 7.79/1.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f41,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.79/1.53    inference(ennf_transformation,[],[f14])).
% 7.79/1.53  
% 7.79/1.53  fof(f42,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.53    inference(flattening,[],[f41])).
% 7.79/1.53  
% 7.79/1.53  fof(f73,plain,(
% 7.79/1.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f42])).
% 7.79/1.53  
% 7.79/1.53  fof(f74,plain,(
% 7.79/1.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f42])).
% 7.79/1.53  
% 7.79/1.53  fof(f75,plain,(
% 7.79/1.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f42])).
% 7.79/1.53  
% 7.79/1.53  fof(f1,axiom,(
% 7.79/1.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f19,plain,(
% 7.79/1.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.79/1.53    inference(ennf_transformation,[],[f1])).
% 7.79/1.53  
% 7.79/1.53  fof(f20,plain,(
% 7.79/1.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.79/1.53    inference(flattening,[],[f19])).
% 7.79/1.53  
% 7.79/1.53  fof(f58,plain,(
% 7.79/1.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f20])).
% 7.79/1.53  
% 7.79/1.53  fof(f84,plain,(
% 7.79/1.53    ~v2_struct_0(sK3)),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f11,axiom,(
% 7.79/1.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f36,plain,(
% 7.79/1.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.79/1.53    inference(ennf_transformation,[],[f11])).
% 7.79/1.53  
% 7.79/1.53  fof(f70,plain,(
% 7.79/1.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f36])).
% 7.79/1.53  
% 7.79/1.53  fof(f10,axiom,(
% 7.79/1.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f35,plain,(
% 7.79/1.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.79/1.53    inference(ennf_transformation,[],[f10])).
% 7.79/1.53  
% 7.79/1.53  fof(f69,plain,(
% 7.79/1.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f35])).
% 7.79/1.53  
% 7.79/1.53  fof(f12,axiom,(
% 7.79/1.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f37,plain,(
% 7.79/1.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.79/1.53    inference(ennf_transformation,[],[f12])).
% 7.79/1.53  
% 7.79/1.53  fof(f38,plain,(
% 7.79/1.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.79/1.53    inference(flattening,[],[f37])).
% 7.79/1.53  
% 7.79/1.53  fof(f71,plain,(
% 7.79/1.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f38])).
% 7.79/1.53  
% 7.79/1.53  fof(f15,axiom,(
% 7.79/1.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f43,plain,(
% 7.79/1.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.79/1.53    inference(ennf_transformation,[],[f15])).
% 7.79/1.53  
% 7.79/1.53  fof(f76,plain,(
% 7.79/1.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f43])).
% 7.79/1.53  
% 7.79/1.53  fof(f2,axiom,(
% 7.79/1.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f21,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.79/1.53    inference(ennf_transformation,[],[f2])).
% 7.79/1.53  
% 7.79/1.53  fof(f22,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.79/1.53    inference(flattening,[],[f21])).
% 7.79/1.53  
% 7.79/1.53  fof(f59,plain,(
% 7.79/1.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f22])).
% 7.79/1.53  
% 7.79/1.53  fof(f8,axiom,(
% 7.79/1.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f31,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.79/1.53    inference(ennf_transformation,[],[f8])).
% 7.79/1.53  
% 7.79/1.53  fof(f32,plain,(
% 7.79/1.53    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.79/1.53    inference(flattening,[],[f31])).
% 7.79/1.53  
% 7.79/1.53  fof(f67,plain,(
% 7.79/1.53    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f32])).
% 7.79/1.53  
% 7.79/1.53  fof(f95,plain,(
% 7.79/1.53    ( ! [X6] : (k1_funct_1(sK6,X6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK4))) )),
% 7.79/1.53    inference(cnf_transformation,[],[f57])).
% 7.79/1.53  
% 7.79/1.53  fof(f5,axiom,(
% 7.79/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f26,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.53    inference(ennf_transformation,[],[f5])).
% 7.79/1.53  
% 7.79/1.53  fof(f62,plain,(
% 7.79/1.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.53    inference(cnf_transformation,[],[f26])).
% 7.79/1.53  
% 7.79/1.53  fof(f4,axiom,(
% 7.79/1.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f24,plain,(
% 7.79/1.53    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.79/1.53    inference(ennf_transformation,[],[f4])).
% 7.79/1.53  
% 7.79/1.53  fof(f25,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.79/1.53    inference(flattening,[],[f24])).
% 7.79/1.53  
% 7.79/1.53  fof(f61,plain,(
% 7.79/1.53    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f25])).
% 7.79/1.53  
% 7.79/1.53  fof(f65,plain,(
% 7.79/1.53    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f50])).
% 7.79/1.53  
% 7.79/1.53  fof(f3,axiom,(
% 7.79/1.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.79/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.53  
% 7.79/1.53  fof(f23,plain,(
% 7.79/1.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.79/1.53    inference(ennf_transformation,[],[f3])).
% 7.79/1.53  
% 7.79/1.53  fof(f60,plain,(
% 7.79/1.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.79/1.53    inference(cnf_transformation,[],[f23])).
% 7.79/1.53  
% 7.79/1.53  cnf(c_31,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK3,sK1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f85]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1248,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK3,sK1) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_31]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1960,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26,negated_conjecture,
% 7.79/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 7.79/1.53      inference(cnf_transformation,[],[f90]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1253,negated_conjecture,
% 7.79/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_26]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1955,plain,
% 7.79/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_14,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.79/1.53      | ~ m1_pre_topc(X3,X1)
% 7.79/1.53      | ~ m1_pre_topc(X3,X4)
% 7.79/1.53      | ~ m1_pre_topc(X1,X4)
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.79/1.53      | v2_struct_0(X4)
% 7.79/1.53      | v2_struct_0(X2)
% 7.79/1.53      | ~ l1_pre_topc(X4)
% 7.79/1.53      | ~ l1_pre_topc(X2)
% 7.79/1.53      | ~ v2_pre_topc(X4)
% 7.79/1.53      | ~ v2_pre_topc(X2)
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1264,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 7.79/1.53      | ~ m1_pre_topc(X2_56,X3_56)
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X3_56)
% 7.79/1.53      | ~ m1_pre_topc(X2_56,X0_56)
% 7.79/1.53      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 7.79/1.53      | v2_struct_0(X3_56)
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v1_funct_1(X0_55)
% 7.79/1.53      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_14]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1944,plain,
% 7.79/1.53      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)
% 7.79/1.53      | v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 7.79/1.53      | m1_pre_topc(X2_56,X3_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X0_56,X3_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 7.79/1.53      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 7.79/1.53      | v2_struct_0(X3_56) = iProver_top
% 7.79/1.53      | v2_struct_0(X1_56) = iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(X3_56) != iProver_top
% 7.79/1.53      | v2_pre_topc(X3_56) != iProver_top
% 7.79/1.53      | v2_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | v1_funct_1(X0_55) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4089,plain,
% 7.79/1.53      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5)
% 7.79/1.53      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X0_56,sK4) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,X1_56) != iProver_top
% 7.79/1.53      | v2_struct_0(X1_56) = iProver_top
% 7.79/1.53      | v2_struct_0(sK2) = iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v2_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1955,c_1944]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_8,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.79/1.53      inference(cnf_transformation,[],[f66]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1268,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.79/1.53      | ~ v1_funct_1(X0_55)
% 7.79/1.53      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_8]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1940,plain,
% 7.79/1.53      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 7.79/1.53      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.79/1.53      | v1_funct_1(X2_55) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3666,plain,
% 7.79/1.53      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55)
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1955,c_1940]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_28,negated_conjecture,
% 7.79/1.53      ( v1_funct_1(sK5) ),
% 7.79/1.53      inference(cnf_transformation,[],[f88]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2380,plain,
% 7.79/1.53      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | ~ v1_funct_1(sK5)
% 7.79/1.53      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1268]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4016,plain,
% 7.79/1.53      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_3666,c_28,c_26,c_2380]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4102,plain,
% 7.79/1.53      ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 7.79/1.53      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X1_56,sK4) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,X0_56) != iProver_top
% 7.79/1.53      | v2_struct_0(X0_56) = iProver_top
% 7.79/1.53      | v2_struct_0(sK2) = iProver_top
% 7.79/1.53      | l1_pre_topc(X0_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v2_pre_topc(X0_56) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_4089,c_4016]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_35,negated_conjecture,
% 7.79/1.53      ( ~ v2_struct_0(sK2) ),
% 7.79/1.53      inference(cnf_transformation,[],[f81]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_42,plain,
% 7.79/1.53      ( v2_struct_0(sK2) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_34,negated_conjecture,
% 7.79/1.53      ( v2_pre_topc(sK2) ),
% 7.79/1.53      inference(cnf_transformation,[],[f82]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_43,plain,
% 7.79/1.53      ( v2_pre_topc(sK2) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_33,negated_conjecture,
% 7.79/1.53      ( l1_pre_topc(sK2) ),
% 7.79/1.53      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_44,plain,
% 7.79/1.53      ( l1_pre_topc(sK2) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_49,plain,
% 7.79/1.53      ( v1_funct_1(sK5) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_27,negated_conjecture,
% 7.79/1.53      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 7.79/1.53      inference(cnf_transformation,[],[f89]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_50,plain,
% 7.79/1.53      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6598,plain,
% 7.79/1.53      ( l1_pre_topc(X0_56) != iProver_top
% 7.79/1.53      | k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 7.79/1.53      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X1_56,sK4) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,X0_56) != iProver_top
% 7.79/1.53      | v2_struct_0(X0_56) = iProver_top
% 7.79/1.53      | v2_pre_topc(X0_56) != iProver_top ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_4102,c_42,c_43,c_44,c_49,c_50]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6599,plain,
% 7.79/1.53      ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 7.79/1.53      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.79/1.53      | m1_pre_topc(X1_56,sK4) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,X0_56) != iProver_top
% 7.79/1.53      | v2_struct_0(X0_56) = iProver_top
% 7.79/1.53      | l1_pre_topc(X0_56) != iProver_top
% 7.79/1.53      | v2_pre_topc(X0_56) != iProver_top ),
% 7.79/1.53      inference(renaming,[status(thm)],[c_6598]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6613,plain,
% 7.79/1.53      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3))
% 7.79/1.53      | m1_pre_topc(sK4,sK1) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK3,sK4) != iProver_top
% 7.79/1.53      | v2_struct_0(sK1) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK1) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK1) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1960,c_6599]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_38,negated_conjecture,
% 7.79/1.53      ( ~ v2_struct_0(sK1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f78]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_39,plain,
% 7.79/1.53      ( v2_struct_0(sK1) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_37,negated_conjecture,
% 7.79/1.53      ( v2_pre_topc(sK1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_40,plain,
% 7.79/1.53      ( v2_pre_topc(sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_36,negated_conjecture,
% 7.79/1.53      ( l1_pre_topc(sK1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_41,plain,
% 7.79/1.53      ( l1_pre_topc(sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_29,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK4,sK1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f87]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_48,plain,
% 7.79/1.53      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_25,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK3,sK4) ),
% 7.79/1.53      inference(cnf_transformation,[],[f91]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_52,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7085,plain,
% 7.79/1.53      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_6613,c_39,c_40,c_41,c_48,c_52]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6,plain,
% 7.79/1.53      ( r2_funct_2(X0,X1,X2,X3)
% 7.79/1.53      | ~ v1_funct_2(X3,X0,X1)
% 7.79/1.53      | ~ v1_funct_2(X2,X0,X1)
% 7.79/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.53      | m1_subset_1(sK0(X0,X2,X3),X0)
% 7.79/1.53      | ~ v1_funct_1(X2)
% 7.79/1.53      | ~ v1_funct_1(X3) ),
% 7.79/1.53      inference(cnf_transformation,[],[f64]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_20,negated_conjecture,
% 7.79/1.53      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
% 7.79/1.53      inference(cnf_transformation,[],[f96]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_711,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.53      | ~ v1_funct_2(X3,X1,X2)
% 7.79/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | m1_subset_1(sK0(X1,X3,X0),X1)
% 7.79/1.53      | ~ v1_funct_1(X3)
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != X3
% 7.79/1.53      | u1_struct_0(sK2) != X2
% 7.79/1.53      | u1_struct_0(sK3) != X1
% 7.79/1.53      | sK6 != X0 ),
% 7.79/1.53      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_712,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
% 7.79/1.53      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | ~ v1_funct_1(sK6) ),
% 7.79/1.53      inference(unflattening,[status(thm)],[c_711]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_24,negated_conjecture,
% 7.79/1.53      ( v1_funct_1(sK6) ),
% 7.79/1.53      inference(cnf_transformation,[],[f92]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_23,negated_conjecture,
% 7.79/1.53      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 7.79/1.53      inference(cnf_transformation,[],[f93]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_22,negated_conjecture,
% 7.79/1.53      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 7.79/1.53      inference(cnf_transformation,[],[f94]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_714,plain,
% 7.79/1.53      ( ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_712,c_24,c_23,c_22]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_715,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) ),
% 7.79/1.53      inference(renaming,[status(thm)],[c_714]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1237,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_715]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1971,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_46,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_51,plain,
% 7.79/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_716,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_17,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.79/1.53      | ~ m1_pre_topc(X3,X4)
% 7.79/1.53      | ~ m1_pre_topc(X1,X4)
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.79/1.53      | v2_struct_0(X4)
% 7.79/1.53      | v2_struct_0(X2)
% 7.79/1.53      | ~ l1_pre_topc(X4)
% 7.79/1.53      | ~ l1_pre_topc(X2)
% 7.79/1.53      | ~ v2_pre_topc(X4)
% 7.79/1.53      | ~ v2_pre_topc(X2)
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.79/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1261,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 7.79/1.53      | ~ m1_pre_topc(X2_56,X3_56)
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X3_56)
% 7.79/1.53      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 7.79/1.53      | v2_struct_0(X3_56)
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v1_funct_1(X0_55)
% 7.79/1.53      | v1_funct_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_17]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2415,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X1_56)
% 7.79/1.53      | ~ m1_pre_topc(sK4,X1_56)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | v1_funct_1(k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5))
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1261]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2535,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X0_56,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5))
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2415]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2650,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK3,sK1)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2535]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2651,plain,
% 7.79/1.53      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,sK1) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK3,sK1) != iProver_top
% 7.79/1.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | v2_struct_0(sK1) = iProver_top
% 7.79/1.53      | v2_struct_0(sK2) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK1) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK1) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) = iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_2650]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_16,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.79/1.53      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.79/1.53      | ~ m1_pre_topc(X4,X3)
% 7.79/1.53      | ~ m1_pre_topc(X1,X3)
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.79/1.53      | v2_struct_0(X3)
% 7.79/1.53      | v2_struct_0(X2)
% 7.79/1.53      | ~ l1_pre_topc(X3)
% 7.79/1.53      | ~ l1_pre_topc(X2)
% 7.79/1.53      | ~ v2_pre_topc(X3)
% 7.79/1.53      | ~ v2_pre_topc(X2)
% 7.79/1.53      | ~ v1_funct_1(X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f74]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1262,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 7.79/1.53      | v1_funct_2(k3_tmap_1(X2_56,X1_56,X0_56,X3_56,X0_55),u1_struct_0(X3_56),u1_struct_0(X1_56))
% 7.79/1.53      | ~ m1_pre_topc(X3_56,X2_56)
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X2_56)
% 7.79/1.53      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 7.79/1.53      | v2_struct_0(X2_56)
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X2_56)
% 7.79/1.53      | ~ v2_pre_topc(X2_56)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v1_funct_1(X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_16]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2431,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5),u1_struct_0(X1_56),u1_struct_0(sK2))
% 7.79/1.53      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X1_56,X0_56)
% 7.79/1.53      | ~ m1_pre_topc(sK4,X0_56)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(X0_56)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(X0_56)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(X0_56)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1262]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2564,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5),u1_struct_0(X0_56),u1_struct_0(sK2))
% 7.79/1.53      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X0_56,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2431]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2696,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK3,sK1)
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2564]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2697,plain,
% 7.79/1.53      ( v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 7.79/1.53      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,sK1) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK3,sK1) != iProver_top
% 7.79/1.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | v2_struct_0(sK1) = iProver_top
% 7.79/1.53      | v2_struct_0(sK2) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK1) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK1) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_2696]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_15,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.79/1.53      | ~ m1_pre_topc(X3,X4)
% 7.79/1.53      | ~ m1_pre_topc(X1,X4)
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.79/1.53      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.79/1.53      | v2_struct_0(X4)
% 7.79/1.53      | v2_struct_0(X2)
% 7.79/1.53      | ~ l1_pre_topc(X4)
% 7.79/1.53      | ~ l1_pre_topc(X2)
% 7.79/1.53      | ~ v2_pre_topc(X4)
% 7.79/1.53      | ~ v2_pre_topc(X2)
% 7.79/1.53      | ~ v1_funct_1(X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f75]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1263,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 7.79/1.53      | ~ m1_pre_topc(X2_56,X3_56)
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X3_56)
% 7.79/1.53      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 7.79/1.53      | m1_subset_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 7.79/1.53      | v2_struct_0(X3_56)
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X3_56)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v1_funct_1(X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_15]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2441,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X0_56,X1_56)
% 7.79/1.53      | ~ m1_pre_topc(sK4,X1_56)
% 7.79/1.53      | m1_subset_1(k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(X1_56)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(X1_56)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1263]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2583,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(X0_56,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK2))))
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2441]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2713,plain,
% 7.79/1.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_pre_topc(sK4,sK1)
% 7.79/1.53      | ~ m1_pre_topc(sK3,sK1)
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v2_struct_0(sK1)
% 7.79/1.53      | v2_struct_0(sK2)
% 7.79/1.53      | ~ l1_pre_topc(sK1)
% 7.79/1.53      | ~ l1_pre_topc(sK2)
% 7.79/1.53      | ~ v2_pre_topc(sK1)
% 7.79/1.53      | ~ v2_pre_topc(sK2)
% 7.79/1.53      | ~ v1_funct_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_2583]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2714,plain,
% 7.79/1.53      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK4,sK1) != iProver_top
% 7.79/1.53      | m1_pre_topc(sK3,sK1) != iProver_top
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 7.79/1.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | v2_struct_0(sK1) = iProver_top
% 7.79/1.53      | v2_struct_0(sK2) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK1) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK1) != iProver_top
% 7.79/1.53      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_2713]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2803,plain,
% 7.79/1.53      ( m1_subset_1(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_1971,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_48,c_49,
% 7.79/1.53                 c_50,c_51,c_716,c_2651,c_2697,c_2714]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_0,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1273,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0_55,X1_55)
% 7.79/1.53      | r2_hidden(X0_55,X1_55)
% 7.79/1.53      | v1_xboole_0(X1_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_0]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1935,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,X1_55) != iProver_top
% 7.79/1.53      | r2_hidden(X0_55,X1_55) = iProver_top
% 7.79/1.53      | v1_xboole_0(X1_55) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2808,plain,
% 7.79/1.53      ( r2_hidden(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_2803,c_1935]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_32,negated_conjecture,
% 7.79/1.53      ( ~ v2_struct_0(sK3) ),
% 7.79/1.53      inference(cnf_transformation,[],[f84]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_45,plain,
% 7.79/1.53      ( v2_struct_0(sK3) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1254,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK3,sK4) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_25]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1954,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_12,plain,
% 7.79/1.53      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f70]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1265,plain,
% 7.79/1.53      ( ~ m1_pre_topc(X0_56,X1_56)
% 7.79/1.53      | ~ l1_pre_topc(X1_56)
% 7.79/1.53      | l1_pre_topc(X0_56) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_12]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1943,plain,
% 7.79/1.53      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(X0_56) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3085,plain,
% 7.79/1.53      ( l1_pre_topc(sK4) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK3) = iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1954,c_1943]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1250,negated_conjecture,
% 7.79/1.53      ( m1_pre_topc(sK4,sK1) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_29]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1958,plain,
% 7.79/1.53      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3086,plain,
% 7.79/1.53      ( l1_pre_topc(sK4) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK1) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1958,c_1943]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_11,plain,
% 7.79/1.53      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_13,plain,
% 7.79/1.53      ( v2_struct_0(X0)
% 7.79/1.53      | ~ l1_struct_0(X0)
% 7.79/1.53      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.79/1.53      inference(cnf_transformation,[],[f71]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_412,plain,
% 7.79/1.53      ( v2_struct_0(X0)
% 7.79/1.53      | ~ l1_pre_topc(X0)
% 7.79/1.53      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.79/1.53      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1240,plain,
% 7.79/1.53      ( v2_struct_0(X0_56)
% 7.79/1.53      | ~ l1_pre_topc(X0_56)
% 7.79/1.53      | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_412]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3311,plain,
% 7.79/1.53      ( v2_struct_0(sK3)
% 7.79/1.53      | ~ l1_pre_topc(sK3)
% 7.79/1.53      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1240]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3312,plain,
% 7.79/1.53      ( v2_struct_0(sK3) = iProver_top
% 7.79/1.53      | l1_pre_topc(sK3) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_3311]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_5209,plain,
% 7.79/1.53      ( r2_hidden(sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_2808,c_41,c_45,c_3085,c_3086,c_3312]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7091,plain,
% 7.79/1.53      ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(sK3)) = iProver_top ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_7085,c_5209]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_18,plain,
% 7.79/1.53      ( ~ m1_pre_topc(X0,X1)
% 7.79/1.53      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.53      | ~ l1_pre_topc(X1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f76]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1260,plain,
% 7.79/1.53      ( ~ m1_pre_topc(X0_56,X1_56)
% 7.79/1.53      | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56)))
% 7.79/1.53      | ~ l1_pre_topc(X1_56) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_18]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1948,plain,
% 7.79/1.53      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.79/1.53      | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56))) = iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1,plain,
% 7.79/1.53      ( m1_subset_1(X0,X1)
% 7.79/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.79/1.53      | ~ r2_hidden(X0,X2) ),
% 7.79/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1272,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,X1_55)
% 7.79/1.53      | ~ m1_subset_1(X2_55,k1_zfmisc_1(X1_55))
% 7.79/1.53      | ~ r2_hidden(X0_55,X2_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_1]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1936,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,X1_55) = iProver_top
% 7.79/1.53      | m1_subset_1(X2_55,k1_zfmisc_1(X1_55)) != iProver_top
% 7.79/1.53      | r2_hidden(X0_55,X2_55) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3496,plain,
% 7.79/1.53      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.79/1.53      | m1_subset_1(X0_55,u1_struct_0(X1_56)) = iProver_top
% 7.79/1.53      | r2_hidden(X0_55,u1_struct_0(X0_56)) != iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1948,c_1936]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7188,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,X0_56) != iProver_top
% 7.79/1.53      | m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(X0_56)) = iProver_top
% 7.79/1.53      | l1_pre_topc(X0_56) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_7091,c_3496]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_9,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.53      | ~ m1_subset_1(X3,X1)
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | v1_xboole_0(X1)
% 7.79/1.53      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.79/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1267,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 7.79/1.53      | ~ m1_subset_1(X3_55,X1_55)
% 7.79/1.53      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.79/1.53      | ~ v1_funct_1(X0_55)
% 7.79/1.53      | v1_xboole_0(X1_55)
% 7.79/1.53      | k3_funct_2(X1_55,X2_55,X0_55,X3_55) = k1_funct_1(X0_55,X3_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_9]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1941,plain,
% 7.79/1.53      ( k3_funct_2(X0_55,X1_55,X2_55,X3_55) = k1_funct_1(X2_55,X3_55)
% 7.79/1.53      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 7.79/1.53      | m1_subset_1(X3_55,X0_55) != iProver_top
% 7.79/1.53      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.79/1.53      | v1_funct_1(X2_55) != iProver_top
% 7.79/1.53      | v1_xboole_0(X0_55) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3689,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
% 7.79/1.53      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1955,c_1941]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4850,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 7.79/1.53      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_3689,c_49,c_50]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4851,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) = k1_funct_1(sK5,X0_55)
% 7.79/1.53      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(renaming,[status(thm)],[c_4850]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26123,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
% 7.79/1.53      | m1_pre_topc(sK3,sK4) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK4) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_7188,c_4851]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26736,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_26123,c_41,c_52,c_3086]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_21,negated_conjecture,
% 7.79/1.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.79/1.53      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 7.79/1.53      | k1_funct_1(sK6,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f95]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1258,negated_conjecture,
% 7.79/1.53      ( ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 7.79/1.53      | ~ r2_hidden(X0_55,u1_struct_0(sK3))
% 7.79/1.53      | k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_21]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1950,plain,
% 7.79/1.53      ( k1_funct_1(sK6,X0_55) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_55)
% 7.79/1.53      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 7.79/1.53      | r2_hidden(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26124,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
% 7.79/1.53      | m1_pre_topc(sK3,sK4) != iProver_top
% 7.79/1.53      | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6),u1_struct_0(sK3)) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK4) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_7188,c_1950]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26732,plain,
% 7.79/1.53      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_26124,c_41,c_52,c_3086,c_7091]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26740,plain,
% 7.79/1.53      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6))
% 7.79/1.53      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_26736,c_26732]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_4,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | v1_relat_1(X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1269,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 7.79/1.53      | v1_relat_1(X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_4]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1939,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 7.79/1.53      | v1_relat_1(X0_55) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2922,plain,
% 7.79/1.53      ( v1_relat_1(sK5) = iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1955,c_1939]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3,plain,
% 7.79/1.53      ( ~ r2_hidden(X0,X1)
% 7.79/1.53      | ~ v1_relat_1(X2)
% 7.79/1.53      | ~ v1_funct_1(X2)
% 7.79/1.53      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 7.79/1.53      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1270,plain,
% 7.79/1.53      ( ~ r2_hidden(X0_55,X1_55)
% 7.79/1.53      | ~ v1_relat_1(X2_55)
% 7.79/1.53      | ~ v1_funct_1(X2_55)
% 7.79/1.53      | k1_funct_1(k7_relat_1(X2_55,X1_55),X0_55) = k1_funct_1(X2_55,X0_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_3]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1938,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(X0_55,X1_55),X2_55) = k1_funct_1(X0_55,X2_55)
% 7.79/1.53      | r2_hidden(X2_55,X1_55) != iProver_top
% 7.79/1.53      | v1_relat_1(X0_55) != iProver_top
% 7.79/1.53      | v1_funct_1(X0_55) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_5214,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(X0_55,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(X0_55,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
% 7.79/1.53      | v1_relat_1(X0_55) != iProver_top
% 7.79/1.53      | v1_funct_1(X0_55) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_5209,c_1938]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6081,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_2922,c_5214]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2338,plain,
% 7.79/1.53      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 7.79/1.53      | v1_relat_1(sK5) ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2339,plain,
% 7.79/1.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | v1_relat_1(sK5) = iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_5216,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
% 7.79/1.53      | v1_relat_1(sK5) != iProver_top
% 7.79/1.53      | v1_funct_1(sK5) != iProver_top ),
% 7.79/1.53      inference(instantiation,[status(thm)],[c_5214]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_6369,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_6081,c_49,c_51,c_2339,c_5216]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7089,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_7085,c_6369]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_5,plain,
% 7.79/1.53      ( r2_funct_2(X0,X1,X2,X3)
% 7.79/1.53      | ~ v1_funct_2(X3,X0,X1)
% 7.79/1.53      | ~ v1_funct_2(X2,X0,X1)
% 7.79/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.53      | ~ v1_funct_1(X2)
% 7.79/1.53      | ~ v1_funct_1(X3)
% 7.79/1.53      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 7.79/1.53      inference(cnf_transformation,[],[f65]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_731,plain,
% 7.79/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.53      | ~ v1_funct_2(X3,X1,X2)
% 7.79/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.53      | ~ v1_funct_1(X3)
% 7.79/1.53      | ~ v1_funct_1(X0)
% 7.79/1.53      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != X3
% 7.79/1.53      | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
% 7.79/1.53      | u1_struct_0(sK2) != X2
% 7.79/1.53      | u1_struct_0(sK3) != X1
% 7.79/1.53      | sK6 != X0 ),
% 7.79/1.53      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_732,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | ~ v1_funct_1(sK6)
% 7.79/1.53      | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(unflattening,[status(thm)],[c_731]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_734,plain,
% 7.79/1.53      ( ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_732,c_24,c_23,c_22]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_735,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(renaming,[status(thm)],[c_734]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1236,plain,
% 7.79/1.53      ( ~ v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.79/1.53      | ~ m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.79/1.53      | ~ v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5))
% 7.79/1.53      | k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_735]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1972,plain,
% 7.79/1.53      ( k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6))
% 7.79/1.53      | v1_funct_2(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.79/1.53      | m1_subset_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.79/1.53      | v1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5)) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2855,plain,
% 7.79/1.53      ( k1_funct_1(sK6,sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) != k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK0(u1_struct_0(sK3),k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)) ),
% 7.79/1.53      inference(global_propositional_subsumption,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_1972,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_29,c_28,
% 7.79/1.53                 c_27,c_26,c_1236,c_2650,c_2696,c_2713]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7093,plain,
% 7.79/1.53      ( k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_7085,c_2855]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_7110,plain,
% 7.79/1.53      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) != k1_funct_1(sK6,sK0(u1_struct_0(sK3),k7_relat_1(sK5,u1_struct_0(sK3)),sK6)) ),
% 7.79/1.53      inference(demodulation,[status(thm)],[c_7089,c_7093]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26743,plain,
% 7.79/1.53      ( v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.79/1.53      inference(forward_subsumption_resolution,
% 7.79/1.53                [status(thm)],
% 7.79/1.53                [c_26740,c_7110]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_2,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.79/1.53      | ~ r2_hidden(X2,X0)
% 7.79/1.53      | ~ v1_xboole_0(X1) ),
% 7.79/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1271,plain,
% 7.79/1.53      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 7.79/1.53      | ~ r2_hidden(X2_55,X0_55)
% 7.79/1.53      | ~ v1_xboole_0(X1_55) ),
% 7.79/1.53      inference(subtyping,[status(esa)],[c_2]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_1937,plain,
% 7.79/1.53      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 7.79/1.53      | r2_hidden(X2_55,X0_55) != iProver_top
% 7.79/1.53      | v1_xboole_0(X1_55) != iProver_top ),
% 7.79/1.53      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_3494,plain,
% 7.79/1.53      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.79/1.53      | r2_hidden(X0_55,u1_struct_0(X0_56)) != iProver_top
% 7.79/1.53      | l1_pre_topc(X1_56) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(X1_56)) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_1948,c_1937]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_5482,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,X0_56) != iProver_top
% 7.79/1.53      | l1_pre_topc(X0_56) != iProver_top
% 7.79/1.53      | v1_xboole_0(u1_struct_0(X0_56)) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_5209,c_3494]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(c_26745,plain,
% 7.79/1.53      ( m1_pre_topc(sK3,sK4) != iProver_top
% 7.79/1.53      | l1_pre_topc(sK4) != iProver_top ),
% 7.79/1.53      inference(superposition,[status(thm)],[c_26743,c_5482]) ).
% 7.79/1.53  
% 7.79/1.53  cnf(contradiction,plain,
% 7.79/1.53      ( $false ),
% 7.79/1.53      inference(minisat,[status(thm)],[c_26745,c_3086,c_52,c_41]) ).
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.53  
% 7.79/1.53  ------                               Statistics
% 7.79/1.53  
% 7.79/1.53  ------ General
% 7.79/1.53  
% 7.79/1.53  abstr_ref_over_cycles:                  0
% 7.79/1.53  abstr_ref_under_cycles:                 0
% 7.79/1.53  gc_basic_clause_elim:                   0
% 7.79/1.53  forced_gc_time:                         0
% 7.79/1.53  parsing_time:                           0.015
% 7.79/1.53  unif_index_cands_time:                  0.
% 7.79/1.53  unif_index_add_time:                    0.
% 7.79/1.53  orderings_time:                         0.
% 7.79/1.53  out_proof_time:                         0.017
% 7.79/1.53  total_time:                             0.963
% 7.79/1.53  num_of_symbols:                         61
% 7.79/1.53  num_of_terms:                           19914
% 7.79/1.53  
% 7.79/1.53  ------ Preprocessing
% 7.79/1.53  
% 7.79/1.53  num_of_splits:                          0
% 7.79/1.53  num_of_split_atoms:                     0
% 7.79/1.53  num_of_reused_defs:                     0
% 7.79/1.53  num_eq_ax_congr_red:                    32
% 7.79/1.53  num_of_sem_filtered_clauses:            1
% 7.79/1.53  num_of_subtypes:                        3
% 7.79/1.53  monotx_restored_types:                  0
% 7.79/1.53  sat_num_of_epr_types:                   0
% 7.79/1.53  sat_num_of_non_cyclic_types:            0
% 7.79/1.53  sat_guarded_non_collapsed_types:        0
% 7.79/1.53  num_pure_diseq_elim:                    0
% 7.79/1.53  simp_replaced_by:                       0
% 7.79/1.53  res_preprocessed:                       186
% 7.79/1.53  prep_upred:                             0
% 7.79/1.53  prep_unflattend:                        26
% 7.79/1.53  smt_new_axioms:                         0
% 7.79/1.53  pred_elim_cands:                        10
% 7.79/1.53  pred_elim:                              2
% 7.79/1.53  pred_elim_cl:                           1
% 7.79/1.53  pred_elim_cycles:                       9
% 7.79/1.53  merged_defs:                            0
% 7.79/1.53  merged_defs_ncl:                        0
% 7.79/1.53  bin_hyper_res:                          0
% 7.79/1.53  prep_cycles:                            4
% 7.79/1.53  pred_elim_time:                         0.019
% 7.79/1.53  splitting_time:                         0.
% 7.79/1.53  sem_filter_time:                        0.
% 7.79/1.53  monotx_time:                            0.
% 7.79/1.53  subtype_inf_time:                       0.001
% 7.79/1.53  
% 7.79/1.53  ------ Problem properties
% 7.79/1.53  
% 7.79/1.53  clauses:                                38
% 7.79/1.53  conjectures:                            18
% 7.79/1.53  epr:                                    17
% 7.79/1.53  horn:                                   31
% 7.79/1.53  ground:                                 19
% 7.79/1.53  unary:                                  17
% 7.79/1.53  binary:                                 2
% 7.79/1.53  lits:                                   134
% 7.79/1.53  lits_eq:                                9
% 7.79/1.53  fd_pure:                                0
% 7.79/1.53  fd_pseudo:                              0
% 7.79/1.53  fd_cond:                                0
% 7.79/1.53  fd_pseudo_cond:                         0
% 7.79/1.53  ac_symbols:                             0
% 7.79/1.53  
% 7.79/1.53  ------ Propositional Solver
% 7.79/1.53  
% 7.79/1.53  prop_solver_calls:                      30
% 7.79/1.53  prop_fast_solver_calls:                 4154
% 7.79/1.53  smt_solver_calls:                       0
% 7.79/1.53  smt_fast_solver_calls:                  0
% 7.79/1.53  prop_num_of_clauses:                    9206
% 7.79/1.53  prop_preprocess_simplified:             16273
% 7.79/1.53  prop_fo_subsumed:                       760
% 7.79/1.53  prop_solver_time:                       0.
% 7.79/1.53  smt_solver_time:                        0.
% 7.79/1.53  smt_fast_solver_time:                   0.
% 7.79/1.53  prop_fast_solver_time:                  0.
% 7.79/1.53  prop_unsat_core_time:                   0.002
% 7.79/1.53  
% 7.79/1.53  ------ QBF
% 7.79/1.53  
% 7.79/1.53  qbf_q_res:                              0
% 7.79/1.53  qbf_num_tautologies:                    0
% 7.79/1.53  qbf_prep_cycles:                        0
% 7.79/1.53  
% 7.79/1.53  ------ BMC1
% 7.79/1.53  
% 7.79/1.53  bmc1_current_bound:                     -1
% 7.79/1.53  bmc1_last_solved_bound:                 -1
% 7.79/1.53  bmc1_unsat_core_size:                   -1
% 7.79/1.53  bmc1_unsat_core_parents_size:           -1
% 7.79/1.53  bmc1_merge_next_fun:                    0
% 7.79/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.79/1.53  
% 7.79/1.53  ------ Instantiation
% 7.79/1.53  
% 7.79/1.53  inst_num_of_clauses:                    2583
% 7.79/1.53  inst_num_in_passive:                    250
% 7.79/1.53  inst_num_in_active:                     1563
% 7.79/1.53  inst_num_in_unprocessed:                770
% 7.79/1.53  inst_num_of_loops:                      1620
% 7.79/1.53  inst_num_of_learning_restarts:          0
% 7.79/1.53  inst_num_moves_active_passive:          52
% 7.79/1.53  inst_lit_activity:                      0
% 7.79/1.53  inst_lit_activity_moves:                0
% 7.79/1.53  inst_num_tautologies:                   0
% 7.79/1.53  inst_num_prop_implied:                  0
% 7.79/1.53  inst_num_existing_simplified:           0
% 7.79/1.53  inst_num_eq_res_simplified:             0
% 7.79/1.53  inst_num_child_elim:                    0
% 7.79/1.53  inst_num_of_dismatching_blockings:      883
% 7.79/1.53  inst_num_of_non_proper_insts:           2944
% 7.79/1.53  inst_num_of_duplicates:                 0
% 7.79/1.53  inst_inst_num_from_inst_to_res:         0
% 7.79/1.53  inst_dismatching_checking_time:         0.
% 7.79/1.53  
% 7.79/1.53  ------ Resolution
% 7.79/1.53  
% 7.79/1.53  res_num_of_clauses:                     0
% 7.79/1.53  res_num_in_passive:                     0
% 7.79/1.53  res_num_in_active:                      0
% 7.79/1.53  res_num_of_loops:                       190
% 7.79/1.53  res_forward_subset_subsumed:            106
% 7.79/1.53  res_backward_subset_subsumed:           2
% 7.79/1.53  res_forward_subsumed:                   0
% 7.79/1.53  res_backward_subsumed:                  0
% 7.79/1.53  res_forward_subsumption_resolution:     0
% 7.79/1.53  res_backward_subsumption_resolution:    0
% 7.79/1.53  res_clause_to_clause_subsumption:       1550
% 7.79/1.53  res_orphan_elimination:                 0
% 7.79/1.53  res_tautology_del:                      228
% 7.79/1.53  res_num_eq_res_simplified:              0
% 7.79/1.53  res_num_sel_changes:                    0
% 7.79/1.53  res_moves_from_active_to_pass:          0
% 7.79/1.53  
% 7.79/1.53  ------ Superposition
% 7.79/1.53  
% 7.79/1.53  sup_time_total:                         0.
% 7.79/1.53  sup_time_generating:                    0.
% 7.79/1.53  sup_time_sim_full:                      0.
% 7.79/1.53  sup_time_sim_immed:                     0.
% 7.79/1.53  
% 7.79/1.53  sup_num_of_clauses:                     430
% 7.79/1.53  sup_num_in_active:                      309
% 7.79/1.53  sup_num_in_passive:                     121
% 7.79/1.53  sup_num_of_loops:                       323
% 7.79/1.53  sup_fw_superposition:                   327
% 7.79/1.53  sup_bw_superposition:                   185
% 7.79/1.53  sup_immediate_simplified:               122
% 7.79/1.53  sup_given_eliminated:                   0
% 7.79/1.53  comparisons_done:                       0
% 7.79/1.53  comparisons_avoided:                    0
% 7.79/1.53  
% 7.79/1.53  ------ Simplifications
% 7.79/1.53  
% 7.79/1.53  
% 7.79/1.53  sim_fw_subset_subsumed:                 17
% 7.79/1.53  sim_bw_subset_subsumed:                 15
% 7.79/1.53  sim_fw_subsumed:                        35
% 7.79/1.53  sim_bw_subsumed:                        0
% 7.79/1.53  sim_fw_subsumption_res:                 28
% 7.79/1.53  sim_bw_subsumption_res:                 0
% 7.79/1.53  sim_tautology_del:                      2
% 7.79/1.53  sim_eq_tautology_del:                   11
% 7.79/1.53  sim_eq_res_simp:                        0
% 7.79/1.53  sim_fw_demodulated:                     6
% 7.79/1.53  sim_bw_demodulated:                     16
% 7.79/1.53  sim_light_normalised:                   97
% 7.79/1.53  sim_joinable_taut:                      0
% 7.79/1.53  sim_joinable_simp:                      0
% 7.79/1.53  sim_ac_normalised:                      0
% 7.79/1.53  sim_smt_subsumption:                    0
% 7.79/1.53  
%------------------------------------------------------------------------------
