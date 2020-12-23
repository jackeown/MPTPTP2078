%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:02 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  239 (13565 expanded)
%              Number of clauses        :  151 (2007 expanded)
%              Number of leaves         :   21 (5938 expanded)
%              Depth                    :   29
%              Number of atoms          : 1513 (300993 expanded)
%              Number of equality atoms :  336 (17638 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f42])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f43])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
          & X0 = X3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X6) )
     => ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6)
        & X0 = X3
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
              & X0 = X3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                  & X0 = X3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                      & X0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6)
                    & sK3 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                          & X0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5)
                          | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5)
                          | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                        ( ? [X6] :
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
    & sK0 = sK3
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f54,f53,f52,f51,f50,f49,f48])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
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

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_908,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1856,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_919,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1845,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_10,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_566,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X5
    | u1_struct_0(sK1) != X2
    | sK6 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_567,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK4)
    | sK6 = sK4 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_97,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_101,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_569,plain,
    ( sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_39,c_37,c_32,c_31,c_30,c_26,c_25,c_24,c_97,c_101])).

cnf(c_899,plain,
    ( sK6 = sK4 ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_23,negated_conjecture,
    ( sK0 = sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_920,negated_conjecture,
    ( sK0 = sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1869,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1845,c_899,c_920])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_931,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X2_59,X0_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X0_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X0_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X0_59)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1834,plain,
    ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59)
    | v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X2_59,X0_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X0_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_3176,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_59)) = k2_tmap_1(sK0,sK1,sK4,X0_59)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1834])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1829,plain,
    ( k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_2343,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1829])).

cnf(c_53,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2782,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2343,c_53])).

cnf(c_3178,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3176,c_2782])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_48,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_54,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4733,plain,
    ( m1_pre_topc(X0_59,sK0) != iProver_top
    | k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3178,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54])).

cnf(c_4734,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
    | m1_pre_topc(X0_59,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_4739,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1856,c_4734])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_910,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1854,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_1866,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1854,c_920])).

cnf(c_4740,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1866,c_4734])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_2,c_1,c_0])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | k7_relat_1(X0_55,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_1864,plain,
    ( k7_relat_1(X0_55,X0_58) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_4252,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
    inference(superposition,[status(thm)],[c_1869,c_1864])).

cnf(c_4741,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_4740,c_4252])).

cnf(c_18,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_924,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59))
    | ~ v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X0_59,X3_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X2_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X0_59)
    | v2_struct_0(X3_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1841,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
    | m1_pre_topc(X3_59,X2_59) != iProver_top
    | m1_pre_topc(X0_59,X2_59) != iProver_top
    | m1_pre_topc(X0_59,X3_59) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
    | v2_pre_topc(X1_59) != iProver_top
    | v2_pre_topc(X2_59) != iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X3_59) = iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X2_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_5057,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4741,c_1841])).

cnf(c_55,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8595,plain,
    ( v2_struct_0(X0_59) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5057,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54,c_55,c_1866])).

cnf(c_8596,plain,
    ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(renaming,[status(thm)],[c_8595])).

cnf(c_8601,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_8596])).

cnf(c_50,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4893,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_1841])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5952,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0_59,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_59) != iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_53,c_54,c_55])).

cnf(c_5959,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4741,c_5952])).

cnf(c_12146,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8601,c_43,c_50,c_1866,c_5959])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_930,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1835,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) = iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_4895,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_1835])).

cnf(c_100,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_903,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_1861,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_933,plain,
    ( ~ l1_pre_topc(X0_59)
    | l1_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1832,plain,
    ( l1_pre_topc(X0_59) != iProver_top
    | l1_struct_0(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_2517,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1861,c_1832])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_932,plain,
    ( ~ m1_pre_topc(X0_59,X1_59)
    | ~ l1_pre_topc(X1_59)
    | l1_pre_topc(X0_59) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1833,plain,
    ( m1_pre_topc(X0_59,X1_59) != iProver_top
    | l1_pre_topc(X1_59) != iProver_top
    | l1_pre_topc(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_2521,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_1833])).

cnf(c_2775,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2521,c_45])).

cnf(c_2779,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2775,c_1832])).

cnf(c_5306,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4895,c_48,c_53,c_54,c_55,c_102,c_2517,c_2779])).

cnf(c_5,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_934,plain,
    ( ~ r2_funct_2(X0_58,X1_58,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_58,X1_58)
    | ~ v1_funct_2(X0_55,X0_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1831,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_58,X1_58,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_58,X1_58) != iProver_top
    | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_5311,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_1831])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_929,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1836,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_4896,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_1836])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_928,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ l1_struct_0(X1_59)
    | ~ l1_struct_0(X2_59)
    | ~ l1_struct_0(X0_59)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1837,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
    | l1_struct_0(X1_59) != iProver_top
    | l1_struct_0(X2_59) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_2574,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(X0_59) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1837])).

cnf(c_3309,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
    | l1_struct_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_48,c_53,c_54,c_102,c_2517])).

cnf(c_3310,plain,
    ( l1_struct_0(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_4897,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_3310])).

cnf(c_5635,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5311,c_48,c_53,c_54,c_55,c_102,c_2517,c_2779,c_4896,c_4897])).

cnf(c_5636,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_5635])).

cnf(c_12150,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12146,c_5636])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_925,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X2_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1961,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ m1_pre_topc(X2_59,X1_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X1_59,sK1,X0_59,X2_59,X0_55)) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2429,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_59,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55)) ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_2734,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_2880,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_2881,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_927,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X1_59)
    | v2_struct_0(X2_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1959,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_59,X1_59)
    | ~ m1_pre_topc(X2_59,X1_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X1_59,sK1,X0_59,X2_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_2427,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_59,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_2764,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_2922,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_2923,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2922])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_926,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),u1_struct_0(X3_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X3_59,X2_59)
    | ~ m1_pre_topc(X0_59,X2_59)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(X2_59)
    | v2_struct_0(X2_59)
    | v2_struct_0(X1_59)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(X2_59)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1926,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k3_tmap_1(sK0,X1_59,X0_59,X2_59,X0_55),u1_struct_0(X2_59),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X2_59,sK0)
    | ~ m1_pre_topc(X0_59,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_2166,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
    | v1_funct_2(k3_tmap_1(sK0,X1_59,X0_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X1_59))
    | ~ m1_pre_topc(X0_59,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
    | ~ v2_pre_topc(X1_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_3420,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
    | v1_funct_2(k3_tmap_1(sK0,X0_59,sK0,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X0_59))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
    | ~ v2_pre_topc(X0_59)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_59)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_59)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_4742,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3420])).

cnf(c_4743,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_17789,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12150,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_53,c_54,c_55,c_1866,c_2881,c_2923,c_4743])).

cnf(c_21,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_921,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1844,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_1870,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1844,c_899,c_920])).

cnf(c_4887,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4739,c_1870])).

cnf(c_17796,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17789,c_4887])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_922,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1843,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_1871,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1843,c_899,c_920])).

cnf(c_4888,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4739,c_1871])).

cnf(c_17795,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17789,c_4888])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17796,c_17795])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:54:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.98/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.48  
% 7.98/1.48  ------  iProver source info
% 7.98/1.48  
% 7.98/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.48  git: non_committed_changes: false
% 7.98/1.48  git: last_make_outside_of_git: false
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     num_symb
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       true
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  ------ Parsing...
% 7.98/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.98/1.48  ------ Proving...
% 7.98/1.48  ------ Problem Properties 
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  clauses                                 38
% 7.98/1.48  conjectures                             22
% 7.98/1.48  EPR                                     18
% 7.98/1.48  Horn                                    32
% 7.98/1.48  unary                                   21
% 7.98/1.48  binary                                  4
% 7.98/1.48  lits                                    135
% 7.98/1.48  lits eq                                 6
% 7.98/1.48  fd_pure                                 0
% 7.98/1.48  fd_pseudo                               0
% 7.98/1.48  fd_cond                                 0
% 7.98/1.48  fd_pseudo_cond                          1
% 7.98/1.48  AC symbols                              0
% 7.98/1.48  
% 7.98/1.48  ------ Schedule dynamic 5 is on 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  Current options:
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     none
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       false
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ Proving...
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS status Theorem for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  fof(f15,conjecture,(
% 7.98/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f16,negated_conjecture,(
% 7.98/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 7.98/1.48    inference(negated_conjecture,[],[f15])).
% 7.98/1.48  
% 7.98/1.48  fof(f42,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f43,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f42])).
% 7.98/1.48  
% 7.98/1.48  fof(f46,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.98/1.48    inference(nnf_transformation,[],[f43])).
% 7.98/1.48  
% 7.98/1.48  fof(f47,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f46])).
% 7.98/1.48  
% 7.98/1.48  fof(f54,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & X0 = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f53,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f52,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f51,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6) & sK3 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f50,plain,(
% 7.98/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f49,plain,(
% 7.98/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f48,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f55,plain,(
% 7.98/1.48    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f54,f53,f52,f51,f50,f49,f48])).
% 7.98/1.48  
% 7.98/1.48  fof(f83,plain,(
% 7.98/1.48    m1_pre_topc(sK2,sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f94,plain,(
% 7.98/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f9,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f30,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 7.98/1.48    inference(ennf_transformation,[],[f9])).
% 7.98/1.48  
% 7.98/1.48  fof(f31,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.98/1.48    inference(flattening,[],[f30])).
% 7.98/1.48  
% 7.98/1.48  fof(f45,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.98/1.48    inference(nnf_transformation,[],[f31])).
% 7.98/1.48  
% 7.98/1.48  fof(f65,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f45])).
% 7.98/1.48  
% 7.98/1.48  fof(f96,plain,(
% 7.98/1.48    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f79,plain,(
% 7.98/1.48    ~v2_struct_0(sK1)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f81,plain,(
% 7.98/1.48    l1_pre_topc(sK1)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f86,plain,(
% 7.98/1.48    v1_funct_1(sK4)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f87,plain,(
% 7.98/1.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f88,plain,(
% 7.98/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f92,plain,(
% 7.98/1.48    v1_funct_1(sK6)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f93,plain,(
% 7.98/1.48    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f8,axiom,(
% 7.98/1.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f28,plain,(
% 7.98/1.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f8])).
% 7.98/1.48  
% 7.98/1.48  fof(f29,plain,(
% 7.98/1.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f28])).
% 7.98/1.48  
% 7.98/1.48  fof(f64,plain,(
% 7.98/1.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f29])).
% 7.98/1.48  
% 7.98/1.48  fof(f6,axiom,(
% 7.98/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f26,plain,(
% 7.98/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.98/1.48    inference(ennf_transformation,[],[f6])).
% 7.98/1.48  
% 7.98/1.48  fof(f62,plain,(
% 7.98/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f26])).
% 7.98/1.48  
% 7.98/1.48  fof(f95,plain,(
% 7.98/1.48    sK0 = sK3),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f10,axiom,(
% 7.98/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f32,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f10])).
% 7.98/1.48  
% 7.98/1.48  fof(f33,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f32])).
% 7.98/1.48  
% 7.98/1.48  fof(f67,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f33])).
% 7.98/1.48  
% 7.98/1.48  fof(f4,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f22,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.98/1.48    inference(ennf_transformation,[],[f4])).
% 7.98/1.48  
% 7.98/1.48  fof(f23,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.98/1.48    inference(flattening,[],[f22])).
% 7.98/1.48  
% 7.98/1.48  fof(f59,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f23])).
% 7.98/1.48  
% 7.98/1.48  fof(f76,plain,(
% 7.98/1.48    ~v2_struct_0(sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f77,plain,(
% 7.98/1.48    v2_pre_topc(sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f78,plain,(
% 7.98/1.48    l1_pre_topc(sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f80,plain,(
% 7.98/1.48    v2_pre_topc(sK1)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f85,plain,(
% 7.98/1.48    m1_pre_topc(sK3,sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f3,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f17,plain,(
% 7.98/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.98/1.48    inference(pure_predicate_removal,[],[f3])).
% 7.98/1.48  
% 7.98/1.48  fof(f21,plain,(
% 7.98/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.98/1.48    inference(ennf_transformation,[],[f17])).
% 7.98/1.48  
% 7.98/1.48  fof(f58,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f21])).
% 7.98/1.48  
% 7.98/1.48  fof(f1,axiom,(
% 7.98/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f18,plain,(
% 7.98/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.98/1.48    inference(ennf_transformation,[],[f1])).
% 7.98/1.48  
% 7.98/1.48  fof(f19,plain,(
% 7.98/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.98/1.48    inference(flattening,[],[f18])).
% 7.98/1.48  
% 7.98/1.48  fof(f56,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f2,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f20,plain,(
% 7.98/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.98/1.48    inference(ennf_transformation,[],[f2])).
% 7.98/1.48  
% 7.98/1.48  fof(f57,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f20])).
% 7.98/1.48  
% 7.98/1.48  fof(f13,axiom,(
% 7.98/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f38,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f13])).
% 7.98/1.48  
% 7.98/1.48  fof(f39,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f38])).
% 7.98/1.48  
% 7.98/1.48  fof(f74,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f39])).
% 7.98/1.48  
% 7.98/1.48  fof(f82,plain,(
% 7.98/1.48    ~v2_struct_0(sK2)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f11,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f34,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f11])).
% 7.98/1.48  
% 7.98/1.48  fof(f35,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f34])).
% 7.98/1.48  
% 7.98/1.48  fof(f70,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f35])).
% 7.98/1.48  
% 7.98/1.48  fof(f7,axiom,(
% 7.98/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f27,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.98/1.48    inference(ennf_transformation,[],[f7])).
% 7.98/1.48  
% 7.98/1.48  fof(f63,plain,(
% 7.98/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f27])).
% 7.98/1.48  
% 7.98/1.48  fof(f5,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f24,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.98/1.48    inference(ennf_transformation,[],[f5])).
% 7.98/1.48  
% 7.98/1.48  fof(f25,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.98/1.48    inference(flattening,[],[f24])).
% 7.98/1.48  
% 7.98/1.48  fof(f44,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.98/1.48    inference(nnf_transformation,[],[f25])).
% 7.98/1.48  
% 7.98/1.48  fof(f60,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f44])).
% 7.98/1.48  
% 7.98/1.48  fof(f69,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f35])).
% 7.98/1.48  
% 7.98/1.48  fof(f68,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f35])).
% 7.98/1.48  
% 7.98/1.48  fof(f12,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.98/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f36,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.98/1.48    inference(ennf_transformation,[],[f12])).
% 7.98/1.48  
% 7.98/1.48  fof(f37,plain,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.98/1.48    inference(flattening,[],[f36])).
% 7.98/1.48  
% 7.98/1.48  fof(f71,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f37])).
% 7.98/1.48  
% 7.98/1.48  fof(f73,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f37])).
% 7.98/1.48  
% 7.98/1.48  fof(f72,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f37])).
% 7.98/1.48  
% 7.98/1.48  fof(f97,plain,(
% 7.98/1.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  fof(f98,plain,(
% 7.98/1.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 7.98/1.48    inference(cnf_transformation,[],[f55])).
% 7.98/1.48  
% 7.98/1.48  cnf(c_35,negated_conjecture,
% 7.98/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_908,negated_conjecture,
% 7.98/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_35]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1856,plain,
% 7.98/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_24,negated_conjecture,
% 7.98/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.98/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_919,negated_conjecture,
% 7.98/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_24]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1845,plain,
% 7.98/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_10,plain,
% 7.98/1.48      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 7.98/1.48      | ~ v1_funct_2(X5,X2,X3)
% 7.98/1.48      | ~ v1_funct_2(X4,X0,X1)
% 7.98/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.98/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.98/1.48      | v1_xboole_0(X1)
% 7.98/1.48      | v1_xboole_0(X3)
% 7.98/1.48      | ~ v1_funct_1(X5)
% 7.98/1.48      | ~ v1_funct_1(X4)
% 7.98/1.48      | X4 = X5 ),
% 7.98/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_22,negated_conjecture,
% 7.98/1.48      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
% 7.98/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_566,plain,
% 7.98/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.98/1.48      | ~ v1_funct_2(X3,X4,X5)
% 7.98/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.98/1.48      | v1_xboole_0(X5)
% 7.98/1.48      | v1_xboole_0(X2)
% 7.98/1.48      | ~ v1_funct_1(X0)
% 7.98/1.48      | ~ v1_funct_1(X3)
% 7.98/1.48      | X3 = X0
% 7.98/1.48      | u1_struct_0(sK3) != X4
% 7.98/1.48      | u1_struct_0(sK0) != X1
% 7.98/1.48      | u1_struct_0(sK1) != X5
% 7.98/1.48      | u1_struct_0(sK1) != X2
% 7.98/1.48      | sK6 != X3
% 7.98/1.48      | sK4 != X0 ),
% 7.98/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_567,plain,
% 7.98/1.48      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.98/1.48      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.98/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.48      | v1_xboole_0(u1_struct_0(sK1))
% 7.98/1.48      | ~ v1_funct_1(sK6)
% 7.98/1.48      | ~ v1_funct_1(sK4)
% 7.98/1.48      | sK6 = sK4 ),
% 7.98/1.48      inference(unflattening,[status(thm)],[c_566]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_39,negated_conjecture,
% 7.98/1.48      ( ~ v2_struct_0(sK1) ),
% 7.98/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_37,negated_conjecture,
% 7.98/1.48      ( l1_pre_topc(sK1) ),
% 7.98/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_32,negated_conjecture,
% 7.98/1.48      ( v1_funct_1(sK4) ),
% 7.98/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_31,negated_conjecture,
% 7.98/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_30,negated_conjecture,
% 7.98/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.98/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_26,negated_conjecture,
% 7.98/1.48      ( v1_funct_1(sK6) ),
% 7.98/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_25,negated_conjecture,
% 7.98/1.48      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_8,plain,
% 7.98/1.48      ( v2_struct_0(X0)
% 7.98/1.48      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.98/1.48      | ~ l1_struct_0(X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_97,plain,
% 7.98/1.48      ( v2_struct_0(sK1)
% 7.98/1.48      | ~ v1_xboole_0(u1_struct_0(sK1))
% 7.98/1.48      | ~ l1_struct_0(sK1) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6,plain,
% 7.98/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_101,plain,
% 7.98/1.49      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_569,plain,
% 7.98/1.49      ( sK6 = sK4 ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_567,c_39,c_37,c_32,c_31,c_30,c_26,c_25,c_24,c_97,
% 7.98/1.49                 c_101]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_899,plain,
% 7.98/1.49      ( sK6 = sK4 ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_569]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_23,negated_conjecture,
% 7.98/1.49      ( sK0 = sK3 ),
% 7.98/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_920,negated_conjecture,
% 7.98/1.49      ( sK0 = sK3 ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1869,plain,
% 7.98/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_1845,c_899,c_920]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_pre_topc(X3,X1)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | ~ v2_pre_topc(X2)
% 7.98/1.49      | ~ v2_pre_topc(X1)
% 7.98/1.49      | v2_struct_0(X1)
% 7.98/1.49      | v2_struct_0(X2)
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | ~ l1_pre_topc(X2)
% 7.98/1.49      | ~ v1_funct_1(X0)
% 7.98/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.98/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_931,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X2_59,X0_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(X0_59)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(X0_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X0_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1834,plain,
% 7.98/1.49      ( k2_partfun1(u1_struct_0(X0_59),u1_struct_0(X1_59),X0_55,u1_struct_0(X2_59)) = k2_tmap_1(X0_59,X1_59,X0_55,X2_59)
% 7.98/1.49      | v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X2_59,X0_59) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(X1_59) != iProver_top
% 7.98/1.49      | v2_pre_topc(X0_59) != iProver_top
% 7.98/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.98/1.49      | l1_pre_topc(X1_59) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0_59) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3176,plain,
% 7.98/1.49      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_59)) = k2_tmap_1(sK0,sK1,sK4,X0_59)
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1869,c_1834]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.49      | ~ v1_funct_1(X0)
% 7.98/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.98/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_936,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1829,plain,
% 7.98/1.49      ( k2_partfun1(X0_58,X1_58,X0_55,X2_58) = k7_relat_1(X0_55,X2_58)
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2343,plain,
% 7.98/1.49      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58)
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1869,c_1829]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_53,plain,
% 7.98/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2782,plain,
% 7.98/1.49      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_58) = k7_relat_1(sK4,X0_58) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_2343,c_53]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3178,plain,
% 7.98/1.49      ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_3176,c_2782]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_42,negated_conjecture,
% 7.98/1.49      ( ~ v2_struct_0(sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_43,plain,
% 7.98/1.49      ( v2_struct_0(sK0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_41,negated_conjecture,
% 7.98/1.49      ( v2_pre_topc(sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_44,plain,
% 7.98/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_40,negated_conjecture,
% 7.98/1.49      ( l1_pre_topc(sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_45,plain,
% 7.98/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_46,plain,
% 7.98/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_38,negated_conjecture,
% 7.98/1.49      ( v2_pre_topc(sK1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_47,plain,
% 7.98/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_48,plain,
% 7.98/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_54,plain,
% 7.98/1.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4733,plain,
% 7.98/1.49      ( m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59)) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_3178,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4734,plain,
% 7.98/1.49      ( k2_tmap_1(sK0,sK1,sK4,X0_59) = k7_relat_1(sK4,u1_struct_0(X0_59))
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_4733]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4739,plain,
% 7.98/1.49      ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1856,c_4734]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_33,negated_conjecture,
% 7.98/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_910,negated_conjecture,
% 7.98/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_33]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1854,plain,
% 7.98/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1866,plain,
% 7.98/1.49      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_1854,c_920]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4740,plain,
% 7.98/1.49      ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1866,c_4734]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.49      | v4_relat_1(X0,X1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_0,plain,
% 7.98/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_544,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.49      | ~ v1_relat_1(X0)
% 7.98/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.98/1.49      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.49      | v1_relat_1(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_548,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.98/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_544,c_2,c_1,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_900,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 7.98/1.49      | k7_relat_1(X0_55,X0_58) = X0_55 ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_548]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1864,plain,
% 7.98/1.49      ( k7_relat_1(X0_55,X0_58) = X0_55
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4252,plain,
% 7.98/1.49      ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1869,c_1864]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4741,plain,
% 7.98/1.49      ( k2_tmap_1(sK0,sK1,sK4,sK0) = sK4 ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_4740,c_4252]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_18,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 7.98/1.49      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 7.98/1.49      | ~ m1_pre_topc(X3,X2)
% 7.98/1.49      | ~ m1_pre_topc(X0,X2)
% 7.98/1.49      | ~ m1_pre_topc(X0,X3)
% 7.98/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.98/1.49      | ~ v2_pre_topc(X1)
% 7.98/1.49      | ~ v2_pre_topc(X2)
% 7.98/1.49      | v2_struct_0(X2)
% 7.98/1.49      | v2_struct_0(X1)
% 7.98/1.49      | v2_struct_0(X0)
% 7.98/1.49      | v2_struct_0(X3)
% 7.98/1.49      | ~ l1_pre_topc(X2)
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | ~ v1_funct_1(X4) ),
% 7.98/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_924,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59))
% 7.98/1.49      | ~ v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X3_59,X2_59)
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X2_59)
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X3_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(X2_59)
% 7.98/1.49      | v2_struct_0(X2_59)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(X0_59)
% 7.98/1.49      | v2_struct_0(X3_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X2_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1841,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(X1_59),k3_tmap_1(X2_59,X1_59,X3_59,X0_59,k2_tmap_1(X2_59,X1_59,X0_55,X3_59)),k2_tmap_1(X2_59,X1_59,X0_55,X0_59)) = iProver_top
% 7.98/1.49      | v1_funct_2(X0_55,u1_struct_0(X2_59),u1_struct_0(X1_59)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X3_59,X2_59) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,X2_59) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,X3_59) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(X1_59) != iProver_top
% 7.98/1.49      | v2_pre_topc(X2_59) != iProver_top
% 7.98/1.49      | v2_struct_0(X2_59) = iProver_top
% 7.98/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.98/1.49      | v2_struct_0(X3_59) = iProver_top
% 7.98/1.49      | l1_pre_topc(X1_59) != iProver_top
% 7.98/1.49      | l1_pre_topc(X2_59) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5057,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4741,c_1841]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_55,plain,
% 7.98/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_8595,plain,
% 7.98/1.49      ( v2_struct_0(X0_59) = iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_5057,c_43,c_44,c_45,c_46,c_47,c_48,c_53,c_54,c_55,
% 7.98/1.49                 c_1866]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_8596,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(X0_59),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_59,sK4),k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_8595]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_8601,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | v2_struct_0(sK2) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4739,c_8596]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_50,plain,
% 7.98/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4893,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,X0_59) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | v2_struct_0(sK2) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4739,c_1841]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_36,negated_conjecture,
% 7.98/1.49      ( ~ v2_struct_0(sK2) ),
% 7.98/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_49,plain,
% 7.98/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5952,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_59,sK2,k2_tmap_1(sK0,sK1,sK4,X0_59)),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 7.98/1.49      | m1_pre_topc(X0_59,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,X0_59) != iProver_top
% 7.98/1.49      | v2_struct_0(X0_59) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_4893,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_53,
% 7.98/1.49                 c_54,c_55]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5959,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 7.98/1.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4741,c_5952]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_12146,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_8601,c_43,c_50,c_1866,c_5959]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_12,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.98/1.49      | ~ l1_struct_0(X1)
% 7.98/1.49      | ~ l1_struct_0(X2)
% 7.98/1.49      | ~ l1_struct_0(X3)
% 7.98/1.49      | ~ v1_funct_1(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_930,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ l1_struct_0(X1_59)
% 7.98/1.49      | ~ l1_struct_0(X2_59)
% 7.98/1.49      | ~ l1_struct_0(X0_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1835,plain,
% 7.98/1.49      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 7.98/1.49      | m1_subset_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(X1_59)))) = iProver_top
% 7.98/1.49      | l1_struct_0(X1_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X2_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4895,plain,
% 7.98/1.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | l1_struct_0(sK0) != iProver_top
% 7.98/1.49      | l1_struct_0(sK1) != iProver_top
% 7.98/1.49      | l1_struct_0(sK2) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4739,c_1835]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_100,plain,
% 7.98/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_102,plain,
% 7.98/1.49      ( l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | l1_struct_0(sK1) = iProver_top ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_100]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_903,negated_conjecture,
% 7.98/1.49      ( l1_pre_topc(sK0) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_40]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1861,plain,
% 7.98/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_933,plain,
% 7.98/1.49      ( ~ l1_pre_topc(X0_59) | l1_struct_0(X0_59) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1832,plain,
% 7.98/1.49      ( l1_pre_topc(X0_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2517,plain,
% 7.98/1.49      ( l1_struct_0(sK0) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1861,c_1832]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7,plain,
% 7.98/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_932,plain,
% 7.98/1.49      ( ~ m1_pre_topc(X0_59,X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | l1_pre_topc(X0_59) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1833,plain,
% 7.98/1.49      ( m1_pre_topc(X0_59,X1_59) != iProver_top
% 7.98/1.49      | l1_pre_topc(X1_59) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0_59) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2521,plain,
% 7.98/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1856,c_1833]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2775,plain,
% 7.98/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_2521,c_45]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2779,plain,
% 7.98/1.49      ( l1_struct_0(sK2) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2775,c_1832]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5306,plain,
% 7.98/1.49      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_4895,c_48,c_53,c_54,c_55,c_102,c_2517,c_2779]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5,plain,
% 7.98/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.98/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.98/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.98/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.98/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.98/1.49      | ~ v1_funct_1(X2)
% 7.98/1.49      | ~ v1_funct_1(X3)
% 7.98/1.49      | X3 = X2 ),
% 7.98/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_934,plain,
% 7.98/1.49      ( ~ r2_funct_2(X0_58,X1_58,X0_55,X1_55)
% 7.98/1.49      | ~ v1_funct_2(X1_55,X0_58,X1_58)
% 7.98/1.49      | ~ v1_funct_2(X0_55,X0_58,X1_58)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 7.98/1.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | ~ v1_funct_1(X1_55)
% 7.98/1.49      | X1_55 = X0_55 ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1831,plain,
% 7.98/1.49      ( X0_55 = X1_55
% 7.98/1.49      | r2_funct_2(X0_58,X1_58,X1_55,X0_55) != iProver_top
% 7.98/1.49      | v1_funct_2(X1_55,X0_58,X1_58) != iProver_top
% 7.98/1.49      | v1_funct_2(X0_55,X0_58,X1_58) != iProver_top
% 7.98/1.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 7.98/1.49      | v1_funct_1(X1_55) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5311,plain,
% 7.98/1.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 7.98/1.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top
% 7.98/1.49      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_5306,c_1831]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_13,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | ~ l1_struct_0(X1)
% 7.98/1.49      | ~ l1_struct_0(X2)
% 7.98/1.49      | ~ l1_struct_0(X3)
% 7.98/1.49      | ~ v1_funct_1(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_929,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ l1_struct_0(X1_59)
% 7.98/1.49      | ~ l1_struct_0(X2_59)
% 7.98/1.49      | ~ l1_struct_0(X0_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1836,plain,
% 7.98/1.49      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 7.98/1.49      | v1_funct_2(k2_tmap_1(X0_59,X1_59,X0_55,X2_59),u1_struct_0(X2_59),u1_struct_0(X1_59)) = iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 7.98/1.49      | l1_struct_0(X1_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X2_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4896,plain,
% 7.98/1.49      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | l1_struct_0(sK0) != iProver_top
% 7.98/1.49      | l1_struct_0(sK1) != iProver_top
% 7.98/1.49      | l1_struct_0(sK2) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4739,c_1836]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_14,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | ~ l1_struct_0(X1)
% 7.98/1.49      | ~ l1_struct_0(X2)
% 7.98/1.49      | ~ l1_struct_0(X3)
% 7.98/1.49      | ~ v1_funct_1(X0)
% 7.98/1.49      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_928,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ l1_struct_0(X1_59)
% 7.98/1.49      | ~ l1_struct_0(X2_59)
% 7.98/1.49      | ~ l1_struct_0(X0_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1837,plain,
% 7.98/1.49      ( v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59)) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59)))) != iProver_top
% 7.98/1.49      | l1_struct_0(X1_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X2_59) != iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top
% 7.98/1.49      | v1_funct_1(k2_tmap_1(X0_59,X1_59,X0_55,X2_59)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2574,plain,
% 7.98/1.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) != iProver_top
% 7.98/1.49      | l1_struct_0(sK0) != iProver_top
% 7.98/1.49      | l1_struct_0(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1869,c_1837]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3309,plain,
% 7.98/1.49      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top
% 7.98/1.49      | l1_struct_0(X0_59) != iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_2574,c_48,c_53,c_54,c_102,c_2517]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3310,plain,
% 7.98/1.49      ( l1_struct_0(X0_59) != iProver_top
% 7.98/1.49      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_59)) = iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_3309]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4897,plain,
% 7.98/1.49      ( l1_struct_0(sK2) != iProver_top
% 7.98/1.49      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_4739,c_3310]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5635,plain,
% 7.98/1.49      ( v1_funct_1(X0_55) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 7.98/1.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_5311,c_48,c_53,c_54,c_55,c_102,c_2517,c_2779,c_4896,
% 7.98/1.49                 c_4897]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5636,plain,
% 7.98/1.49      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 7.98/1.49      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v1_funct_1(X0_55) != iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_5635]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_12150,plain,
% 7.98/1.49      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_12146,c_5636]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_pre_topc(X3,X4)
% 7.98/1.49      | ~ m1_pre_topc(X1,X4)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | ~ v2_pre_topc(X2)
% 7.98/1.49      | ~ v2_pre_topc(X4)
% 7.98/1.49      | v2_struct_0(X4)
% 7.98/1.49      | v2_struct_0(X2)
% 7.98/1.49      | ~ l1_pre_topc(X4)
% 7.98/1.49      | ~ l1_pre_topc(X2)
% 7.98/1.49      | ~ v1_funct_1(X0)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_925,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X2_59)
% 7.98/1.49      | ~ m1_pre_topc(X3_59,X2_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(X2_59)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(X2_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X2_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55)) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1961,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X1_59)
% 7.98/1.49      | ~ m1_pre_topc(X2_59,X1_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(X1_59,sK1,X0_59,X2_59,X0_55)) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_925]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2429,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55)) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_1961]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2734,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55)) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_2429]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2880,plain,
% 7.98/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
% 7.98/1.49      | ~ v1_funct_1(sK4) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_2734]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2881,plain,
% 7.98/1.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) = iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_15,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_pre_topc(X3,X4)
% 7.98/1.49      | ~ m1_pre_topc(X1,X4)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.98/1.49      | ~ v2_pre_topc(X2)
% 7.98/1.49      | ~ v2_pre_topc(X4)
% 7.98/1.49      | v2_struct_0(X4)
% 7.98/1.49      | v2_struct_0(X2)
% 7.98/1.49      | ~ l1_pre_topc(X4)
% 7.98/1.49      | ~ l1_pre_topc(X2)
% 7.98/1.49      | ~ v1_funct_1(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_927,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X2_59)
% 7.98/1.49      | ~ m1_pre_topc(X3_59,X2_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | m1_subset_1(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(X2_59)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(X2_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X2_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1959,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X1_59)
% 7.98/1.49      | ~ m1_pre_topc(X2_59,X1_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
% 7.98/1.49      | m1_subset_1(k3_tmap_1(X1_59,sK1,X0_59,X2_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_59),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_927]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2427,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0_59,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_1959]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2764,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_2427]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2922,plain,
% 7.98/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.98/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(sK4) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_2764]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2923,plain,
% 7.98/1.49      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_2922]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.98/1.49      | ~ m1_pre_topc(X4,X3)
% 7.98/1.49      | ~ m1_pre_topc(X1,X3)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.98/1.49      | ~ v2_pre_topc(X2)
% 7.98/1.49      | ~ v2_pre_topc(X3)
% 7.98/1.49      | v2_struct_0(X3)
% 7.98/1.49      | v2_struct_0(X2)
% 7.98/1.49      | ~ l1_pre_topc(X3)
% 7.98/1.49      | ~ l1_pre_topc(X2)
% 7.98/1.49      | ~ v1_funct_1(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_926,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(X2_59,X1_59,X0_59,X3_59,X0_55),u1_struct_0(X3_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X3_59,X2_59)
% 7.98/1.49      | ~ m1_pre_topc(X0_59,X2_59)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(X2_59)
% 7.98/1.49      | v2_struct_0(X2_59)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(X2_59)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1926,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(sK0,X1_59,X0_59,X2_59,X0_55),u1_struct_0(X2_59),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X2_59,sK0)
% 7.98/1.49      | ~ m1_pre_topc(X0_59,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_926]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2166,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_59),u1_struct_0(X1_59))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(sK0,X1_59,X0_59,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X1_59))
% 7.98/1.49      | ~ m1_pre_topc(X0_59,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_59),u1_struct_0(X1_59))))
% 7.98/1.49      | ~ v2_pre_topc(X1_59)
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | v2_struct_0(X1_59)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | ~ l1_pre_topc(X1_59)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_1926]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3420,plain,
% 7.98/1.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_59))
% 7.98/1.49      | v1_funct_2(k3_tmap_1(sK0,X0_59,sK0,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X0_59))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_59))))
% 7.98/1.49      | ~ v2_pre_topc(X0_59)
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | v2_struct_0(X0_59)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | ~ l1_pre_topc(X0_59)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ v1_funct_1(X0_55) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_2166]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4742,plain,
% 7.98/1.49      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.98/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.98/1.49      | ~ m1_pre_topc(sK0,sK0)
% 7.98/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.98/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK1)
% 7.98/1.49      | v2_struct_0(sK0)
% 7.98/1.49      | v2_struct_0(sK1)
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ l1_pre_topc(sK1)
% 7.98/1.49      | ~ v1_funct_1(sK4) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_3420]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4743,plain,
% 7.98/1.49      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.98/1.49      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.98/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.98/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.98/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v2_struct_0(sK0) = iProver_top
% 7.98/1.49      | v2_struct_0(sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.98/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17789,plain,
% 7.98/1.49      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_12150,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_53,c_54,
% 7.98/1.49                 c_55,c_1866,c_2881,c_2923,c_4743]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_21,negated_conjecture,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 7.98/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_921,negated_conjecture,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1844,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1870,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_1844,c_899,c_920]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4887,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_4739,c_1870]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17796,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_17789,c_4887]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_20,negated_conjecture,
% 7.98/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 7.98/1.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 7.98/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_922,negated_conjecture,
% 7.98/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 7.98/1.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 7.98/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1843,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1871,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_1843,c_899,c_920]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4888,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 7.98/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_4739,c_1871]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17795,plain,
% 7.98/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_17789,c_4888]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(contradiction,plain,
% 7.98/1.49      ( $false ),
% 7.98/1.49      inference(minisat,[status(thm)],[c_17796,c_17795]) ).
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  ------                               Statistics
% 7.98/1.49  
% 7.98/1.49  ------ General
% 7.98/1.49  
% 7.98/1.49  abstr_ref_over_cycles:                  0
% 7.98/1.49  abstr_ref_under_cycles:                 0
% 7.98/1.49  gc_basic_clause_elim:                   0
% 7.98/1.49  forced_gc_time:                         0
% 7.98/1.49  parsing_time:                           0.015
% 7.98/1.49  unif_index_cands_time:                  0.
% 7.98/1.49  unif_index_add_time:                    0.
% 7.98/1.49  orderings_time:                         0.
% 7.98/1.49  out_proof_time:                         0.019
% 7.98/1.49  total_time:                             0.854
% 7.98/1.49  num_of_symbols:                         60
% 7.98/1.49  num_of_terms:                           25442
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing
% 7.98/1.49  
% 7.98/1.49  num_of_splits:                          0
% 7.98/1.49  num_of_split_atoms:                     0
% 7.98/1.49  num_of_reused_defs:                     0
% 7.98/1.49  num_eq_ax_congr_red:                    15
% 7.98/1.49  num_of_sem_filtered_clauses:            1
% 7.98/1.49  num_of_subtypes:                        5
% 7.98/1.49  monotx_restored_types:                  0
% 7.98/1.49  sat_num_of_epr_types:                   0
% 7.98/1.49  sat_num_of_non_cyclic_types:            0
% 7.98/1.49  sat_guarded_non_collapsed_types:        1
% 7.98/1.49  num_pure_diseq_elim:                    0
% 7.98/1.49  simp_replaced_by:                       0
% 7.98/1.49  res_preprocessed:                       200
% 7.98/1.49  prep_upred:                             0
% 7.98/1.49  prep_unflattend:                        12
% 7.98/1.49  smt_new_axioms:                         0
% 7.98/1.49  pred_elim_cands:                        9
% 7.98/1.49  pred_elim:                              4
% 7.98/1.49  pred_elim_cl:                           5
% 7.98/1.49  pred_elim_cycles:                       6
% 7.98/1.49  merged_defs:                            8
% 7.98/1.49  merged_defs_ncl:                        0
% 7.98/1.49  bin_hyper_res:                          8
% 7.98/1.49  prep_cycles:                            4
% 7.98/1.49  pred_elim_time:                         0.003
% 7.98/1.49  splitting_time:                         0.
% 7.98/1.49  sem_filter_time:                        0.
% 7.98/1.49  monotx_time:                            0.
% 7.98/1.49  subtype_inf_time:                       0.001
% 7.98/1.49  
% 7.98/1.49  ------ Problem properties
% 7.98/1.49  
% 7.98/1.49  clauses:                                38
% 7.98/1.49  conjectures:                            22
% 7.98/1.49  epr:                                    18
% 7.98/1.49  horn:                                   32
% 7.98/1.49  ground:                                 23
% 7.98/1.49  unary:                                  21
% 7.98/1.49  binary:                                 4
% 7.98/1.49  lits:                                   135
% 7.98/1.49  lits_eq:                                6
% 7.98/1.49  fd_pure:                                0
% 7.98/1.49  fd_pseudo:                              0
% 7.98/1.49  fd_cond:                                0
% 7.98/1.49  fd_pseudo_cond:                         1
% 7.98/1.49  ac_symbols:                             0
% 7.98/1.49  
% 7.98/1.49  ------ Propositional Solver
% 7.98/1.49  
% 7.98/1.49  prop_solver_calls:                      33
% 7.98/1.49  prop_fast_solver_calls:                 3062
% 7.98/1.49  smt_solver_calls:                       0
% 7.98/1.49  smt_fast_solver_calls:                  0
% 7.98/1.49  prop_num_of_clauses:                    9684
% 7.98/1.49  prop_preprocess_simplified:             18498
% 7.98/1.49  prop_fo_subsumed:                       400
% 7.98/1.49  prop_solver_time:                       0.
% 7.98/1.49  smt_solver_time:                        0.
% 7.98/1.49  smt_fast_solver_time:                   0.
% 7.98/1.49  prop_fast_solver_time:                  0.
% 7.98/1.49  prop_unsat_core_time:                   0.002
% 7.98/1.49  
% 7.98/1.49  ------ QBF
% 7.98/1.49  
% 7.98/1.49  qbf_q_res:                              0
% 7.98/1.49  qbf_num_tautologies:                    0
% 7.98/1.49  qbf_prep_cycles:                        0
% 7.98/1.49  
% 7.98/1.49  ------ BMC1
% 7.98/1.49  
% 7.98/1.49  bmc1_current_bound:                     -1
% 7.98/1.49  bmc1_last_solved_bound:                 -1
% 7.98/1.49  bmc1_unsat_core_size:                   -1
% 7.98/1.49  bmc1_unsat_core_parents_size:           -1
% 7.98/1.49  bmc1_merge_next_fun:                    0
% 7.98/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.98/1.49  
% 7.98/1.49  ------ Instantiation
% 7.98/1.49  
% 7.98/1.49  inst_num_of_clauses:                    2859
% 7.98/1.49  inst_num_in_passive:                    682
% 7.98/1.49  inst_num_in_active:                     946
% 7.98/1.49  inst_num_in_unprocessed:                1231
% 7.98/1.49  inst_num_of_loops:                      1040
% 7.98/1.49  inst_num_of_learning_restarts:          0
% 7.98/1.49  inst_num_moves_active_passive:          88
% 7.98/1.49  inst_lit_activity:                      0
% 7.98/1.49  inst_lit_activity_moves:                0
% 7.98/1.49  inst_num_tautologies:                   0
% 7.98/1.49  inst_num_prop_implied:                  0
% 7.98/1.49  inst_num_existing_simplified:           0
% 7.98/1.49  inst_num_eq_res_simplified:             0
% 7.98/1.49  inst_num_child_elim:                    0
% 7.98/1.49  inst_num_of_dismatching_blockings:      283
% 7.98/1.49  inst_num_of_non_proper_insts:           1944
% 7.98/1.49  inst_num_of_duplicates:                 0
% 7.98/1.49  inst_inst_num_from_inst_to_res:         0
% 7.98/1.49  inst_dismatching_checking_time:         0.
% 7.98/1.49  
% 7.98/1.49  ------ Resolution
% 7.98/1.49  
% 7.98/1.49  res_num_of_clauses:                     0
% 7.98/1.49  res_num_in_passive:                     0
% 7.98/1.49  res_num_in_active:                      0
% 7.98/1.49  res_num_of_loops:                       204
% 7.98/1.49  res_forward_subset_subsumed:            69
% 7.98/1.49  res_backward_subset_subsumed:           0
% 7.98/1.49  res_forward_subsumed:                   0
% 7.98/1.49  res_backward_subsumed:                  0
% 7.98/1.49  res_forward_subsumption_resolution:     0
% 7.98/1.49  res_backward_subsumption_resolution:    0
% 7.98/1.49  res_clause_to_clause_subsumption:       709
% 7.98/1.49  res_orphan_elimination:                 0
% 7.98/1.49  res_tautology_del:                      78
% 7.98/1.49  res_num_eq_res_simplified:              0
% 7.98/1.49  res_num_sel_changes:                    0
% 7.98/1.49  res_moves_from_active_to_pass:          0
% 7.98/1.49  
% 7.98/1.49  ------ Superposition
% 7.98/1.49  
% 7.98/1.49  sup_time_total:                         0.
% 7.98/1.49  sup_time_generating:                    0.
% 7.98/1.49  sup_time_sim_full:                      0.
% 7.98/1.49  sup_time_sim_immed:                     0.
% 7.98/1.49  
% 7.98/1.49  sup_num_of_clauses:                     239
% 7.98/1.49  sup_num_in_active:                      180
% 7.98/1.49  sup_num_in_passive:                     59
% 7.98/1.49  sup_num_of_loops:                       206
% 7.98/1.49  sup_fw_superposition:                   198
% 7.98/1.49  sup_bw_superposition:                   87
% 7.98/1.49  sup_immediate_simplified:               66
% 7.98/1.49  sup_given_eliminated:                   6
% 7.98/1.49  comparisons_done:                       0
% 7.98/1.49  comparisons_avoided:                    0
% 7.98/1.49  
% 7.98/1.49  ------ Simplifications
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  sim_fw_subset_subsumed:                 8
% 7.98/1.49  sim_bw_subset_subsumed:                 10
% 7.98/1.49  sim_fw_subsumed:                        28
% 7.98/1.49  sim_bw_subsumed:                        9
% 7.98/1.49  sim_fw_subsumption_res:                 0
% 7.98/1.49  sim_bw_subsumption_res:                 0
% 7.98/1.49  sim_tautology_del:                      8
% 7.98/1.49  sim_eq_tautology_del:                   13
% 7.98/1.49  sim_eq_res_simp:                        0
% 7.98/1.49  sim_fw_demodulated:                     17
% 7.98/1.49  sim_bw_demodulated:                     14
% 7.98/1.49  sim_light_normalised:                   53
% 7.98/1.49  sim_joinable_taut:                      0
% 7.98/1.49  sim_joinable_simp:                      0
% 7.98/1.49  sim_ac_normalised:                      0
% 7.98/1.49  sim_smt_subsumption:                    0
% 7.98/1.49  
%------------------------------------------------------------------------------
