%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1762+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  175 (2013 expanded)
%              Number of clauses        :  114 ( 439 expanded)
%              Number of leaves         :   15 ( 866 expanded)
%              Depth                    :   31
%              Number of atoms          : 1041 (34561 expanded)
%              Number of equality atoms :  351 (2765 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f39,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK7)
        & ! [X6] :
            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(sK7,X6)
            | ~ r2_hidden(X6,u1_struct_0(X2))
            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)
            & ! [X6] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK6,X6) = k1_funct_1(X5,X6)
                | ~ r2_hidden(X6,u1_struct_0(X2))
                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X4),X5)
                & ! [X6] :
                    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                    | ~ r2_hidden(X6,u1_struct_0(X2))
                    | ~ m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X2,sK5)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X4),X5)
                    & ! [X6] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                        | ~ r2_hidden(X6,u1_struct_0(sK4))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(sK4,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK3),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X4),X5)
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
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,X6) = k1_funct_1(sK7,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK4))
        | ~ m1_subset_1(X6,u1_struct_0(sK5)) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f39,f38,f37,f36,f35,f34])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
                        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f32])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)
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
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
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
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X6] :
      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,X6) = k1_funct_1(sK7,X6)
      | ~ r2_hidden(X6,u1_struct_0(sK4))
      | ~ m1_subset_1(X6,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f47])).

fof(f72,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_841,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1379,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_837,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1383,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(sK1(X1,X2,X0,X4,X3),X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_846,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(sK1(X1_54,X2_54,X0_54,X4_54,X3_54),X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X3_54)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1374,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | m1_subset_1(sK1(X0_54,X1_54,X2_54,X3_54,X4_54),X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | r2_hidden(sK1(X1,X2,X0,X4,X3),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_847,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | r2_hidden(sK1(X1_54,X2_54,X0_54,X4_54,X3_54),X4_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X3_54)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1373,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | r2_hidden(sK1(X0_54,X1_54,X2_54,X3_54,X4_54),X3_54) = iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,X0) = k1_funct_1(sK7,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_842,negated_conjecture,
    ( ~ r2_hidden(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,X0_54) = k1_funct_1(sK7,X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1378,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,X0_54) = k1_funct_1(sK7,X0_54)
    | r2_hidden(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2983,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54)) = k1_funct_1(sK7,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54))
    | k2_partfun1(X0_54,X1_54,X2_54,u1_struct_0(sK4)) = X3_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X3_54,u1_struct_0(sK4),X1_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_54))) != iProver_top
    | m1_subset_1(sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_1378])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_850,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1970,plain,
    ( ~ m1_pre_topc(sK5,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_2327,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_2328,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_838,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1382,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_1370,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_2412,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_1370])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_335,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_824,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_3648,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_3649,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3648])).

cnf(c_3684,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_2(X3_54,u1_struct_0(sK4),X1_54) != iProver_top
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | k2_partfun1(X0_54,X1_54,X2_54,u1_struct_0(sK4)) = X3_54
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54)) = k1_funct_1(sK7,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54))
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2983,c_34,c_38,c_41,c_2328,c_2412,c_3649])).

cnf(c_3685,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54)) = k1_funct_1(sK7,sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54))
    | k2_partfun1(X0_54,X1_54,X2_54,u1_struct_0(sK4)) = X3_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X3_54,u1_struct_0(sK4),X1_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_54))) != iProver_top
    | m1_subset_1(sK1(X0_54,X1_54,X2_54,u1_struct_0(sK4),X3_54),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3684])).

cnf(c_3702,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54))
    | k2_partfun1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK5),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK4),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_3685])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_845,plain,
    ( m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1663,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_pre_topc(sK4,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_1664,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_4079,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54))
    | k2_partfun1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK5),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK4),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_34,c_38,c_41,c_45,c_1664,c_2328,c_2412,c_3649])).

cnf(c_4080,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4),X2_54))
    | k2_partfun1(u1_struct_0(sK5),X0_54,X1_54,u1_struct_0(sK4)) = X2_54
    | v1_funct_2(X1_54,u1_struct_0(sK5),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(sK4),X0_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),X0_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4079])).

cnf(c_4095,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_4080])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_832,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1388,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_851,plain,
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

cnf(c_1369,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_2166,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK3,sK5,X0_55,sK6)
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_1369])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3553,plain,
    ( v2_pre_topc(X1_55) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK3,sK5,X0_55,sK6)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2166,c_35,c_36,c_37,c_42,c_43])).

cnf(c_3554,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK3,sK5,X0_55,sK6)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3553])).

cnf(c_3568,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1388,c_3554])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1705,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_pre_topc(sK4,X1_55)
    | ~ m1_pre_topc(sK4,sK5)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_55),X0_54,u1_struct_0(sK4)) = k3_tmap_1(X1_55,X0_55,sK5,sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_1955,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_55),X0_54,u1_struct_0(sK4)) = k3_tmap_1(sK2,X0_55,sK5,sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_1957,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_3678,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3568,c_31,c_30,c_29,c_28,c_27,c_26,c_24,c_22,c_21,c_20,c_19,c_18,c_1957])).

cnf(c_4165,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4095,c_3678])).

cnf(c_77,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_79,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_84,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_86,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_4205,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = X0_54
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_35,c_37,c_42,c_43,c_79,c_86])).

cnf(c_4206,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),X0_54))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = X0_54
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4205])).

cnf(c_4217,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_4206])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_46,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_47,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4278,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4217,c_46,c_47])).

cnf(c_4279,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4278])).

cnf(c_1396,plain,
    ( v1_xboole_0(u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_4285,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4279,c_1396])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4286,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4285])).

cnf(c_4316,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7)) = k1_funct_1(sK7,sK1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4),sK7))
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4285,c_34,c_40,c_41,c_2328])).

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
    | k3_funct_2(X1,X2,X0,sK1(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK1(X1,X2,X0,X4,X3))
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_848,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | ~ v1_funct_1(X3_54)
    | ~ v1_funct_1(X0_54)
    | k3_funct_2(X1_54,X2_54,X0_54,sK1(X1_54,X2_54,X0_54,X4_54,X3_54)) != k1_funct_1(X3_54,sK1(X1_54,X2_54,X0_54,X4_54,X3_54))
    | k2_partfun1(X1_54,X2_54,X0_54,X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1372,plain,
    ( k3_funct_2(X0_54,X1_54,X2_54,sK1(X0_54,X1_54,X2_54,X3_54,X4_54)) != k1_funct_1(X4_54,sK1(X0_54,X1_54,X2_54,X3_54,X4_54))
    | k2_partfun1(X0_54,X1_54,X2_54,X3_54) = X4_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X4_54,X3_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X3_54,X1_54))) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_4320,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = sK7
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_1372])).

cnf(c_4321,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4320,c_3678])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4324,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4321,c_34,c_35,c_37,c_38,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_79,c_86,c_1664,c_2328,c_2412,c_3649])).

cnf(c_4330,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4324,c_1396])).

cnf(c_40,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4372,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4330,c_34,c_40,c_41,c_2328])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_355,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) != X0
    | u1_struct_0(sK3) != X2
    | u1_struct_0(sK4) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_356,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6))
    | sK7 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_823,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6))
    | sK7 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1397,plain,
    ( sK7 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_4378,plain,
    ( sK7 != sK7
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4372,c_1397])).

cnf(c_4379,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4378])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4379,c_48,c_47,c_46])).


%------------------------------------------------------------------------------
