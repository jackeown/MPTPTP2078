%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:02 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  252 (13069 expanded)
%              Number of clauses        :  162 (1955 expanded)
%              Number of leaves         :   22 (5708 expanded)
%              Depth                    :   29
%              Number of atoms          : 1583 (289733 expanded)
%              Number of equality atoms :  395 (17100 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(nnf_transformation,[],[f44])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f55,f54,f53,f52,f51,f50,f49])).

fof(f85,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f56])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_935,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1933,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_946,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1922,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_576,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_577,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK4)
    | sK6 = sK4 ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_98,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_102,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_579,plain,
    ( sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_40,c_38,c_33,c_32,c_31,c_27,c_26,c_25,c_98,c_102])).

cnf(c_926,plain,
    ( sK6 = sK4 ),
    inference(subtyping,[status(esa)],[c_579])).

cnf(c_24,negated_conjecture,
    ( sK0 = sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_947,negated_conjecture,
    ( sK0 = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1946,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1922,c_926,c_947])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_958,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_55,X2_58) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1911,plain,
    ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_55,X2_58)
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_3800,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_58)) = k2_tmap_1(sK0,sK1,sK4,X0_58)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1911])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X0_57,X1_57,X0_55,X2_57) = k7_relat_1(X0_55,X2_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1906,plain,
    ( k2_partfun1(X0_57,X1_57,X0_55,X2_57) = k7_relat_1(X0_55,X2_57)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_2638,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1906])).

cnf(c_54,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2962,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2638,c_54])).

cnf(c_3802,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58))
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3800,c_2962])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_45,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_47,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_48,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_55,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4221,plain,
    ( m1_pre_topc(X0_58,sK0) != iProver_top
    | k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3802,c_44,c_45,c_46,c_47,c_48,c_49,c_54,c_55])).

cnf(c_4222,plain,
    ( k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58))
    | m1_pre_topc(X0_58,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4221])).

cnf(c_4227,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1933,c_4222])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_937,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1931,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1943,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1931,c_947])).

cnf(c_4228,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1943,c_4222])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_951,plain,
    ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,X3_58,X0_58,k2_tmap_1(X2_58,X1_58,X0_55,X3_58)),k2_tmap_1(X2_58,X1_58,X0_55,X0_58))
    | ~ v1_funct_2(X0_55,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X3_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1918,plain,
    ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,X3_58,X0_58,k2_tmap_1(X2_58,X1_58,X0_55,X3_58)),k2_tmap_1(X2_58,X1_58,X0_55,X0_58)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X3_58,X2_58) != iProver_top
    | m1_pre_topc(X0_58,X2_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X2_58) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X2_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_4339,plain,
    ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_1918])).

cnf(c_56,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5204,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4339,c_44,c_45,c_46,c_47,c_48,c_49,c_54,c_55,c_56,c_1943])).

cnf(c_5205,plain,
    ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_5204])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,X0_57) = X0_55 ),
    inference(subtyping,[status(esa)],[c_556])).

cnf(c_1941,plain,
    ( k7_relat_1(X0_55,X0_57) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_4359,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1941])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_964,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1905,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_relat_1(X1_55)
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1904,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | v1_relat_1(X1_55) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_2420,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1904])).

cnf(c_2851,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_2420])).

cnf(c_4451,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4359,c_2851])).

cnf(c_5210,plain,
    ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,sK4),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5205,c_4451])).

cnf(c_5214,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_5210])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_50,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_51,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5223,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5214,c_50,c_51])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_957,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X2_58)
    | ~ l1_struct_0(X0_58)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1912,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) = iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_957])).

cnf(c_6,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_961,plain,
    ( ~ r2_funct_2(X0_57,X1_57,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_57,X1_57)
    | ~ v1_funct_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1908,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_57,X1_57,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_57,X1_57) != iProver_top
    | v1_funct_2(X0_55,X0_57,X1_57) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_3341,plain,
    ( k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1908])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_956,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X2_58)
    | ~ l1_struct_0(X0_58)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1027,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_955,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X2_58)
    | ~ l1_struct_0(X0_58)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1030,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_4843,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3341,c_1027,c_1030])).

cnf(c_4844,plain,
    ( k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_4843])).

cnf(c_4850,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_4844])).

cnf(c_4853,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4850,c_4227])).

cnf(c_101,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_103,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_930,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_1938,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_960,plain,
    ( ~ l1_pre_topc(X0_58)
    | l1_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1909,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | l1_struct_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_2587,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1909])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_959,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ l1_pre_topc(X1_58)
    | l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1910,plain,
    ( m1_pre_topc(X0_58,X1_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_2591,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1910])).

cnf(c_2844,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_46])).

cnf(c_2848,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_1909])).

cnf(c_1913,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_4236,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_1913])).

cnf(c_1914,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | l1_struct_0(X1_58) != iProver_top
    | l1_struct_0(X2_58) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_3233,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1914])).

cnf(c_3441,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
    | l1_struct_0(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_49,c_54,c_55,c_103,c_2587])).

cnf(c_3442,plain,
    ( l1_struct_0(X0_58) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3441])).

cnf(c_4237,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_3442])).

cnf(c_4235,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_1912])).

cnf(c_4782,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4235,c_49,c_54,c_55,c_56,c_103,c_2587,c_2848])).

cnf(c_4787,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4782,c_1908])).

cnf(c_5108,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_49,c_54,c_55,c_56,c_103,c_2587,c_2848,c_4236,c_4237,c_4787])).

cnf(c_5109,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_5108])).

cnf(c_5227,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5223,c_5109])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_952,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2040,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X1_58,sK1,X0_58,X2_58,X0_55)) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_2499,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_58,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0_58,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_2803,plain,
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
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_2948,plain,
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
    inference(instantiation,[status(thm)],[c_2803])).

cnf(c_2949,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2948])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_954,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2038,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X1_58,sK1,X0_58,X2_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_2497,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_58,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_2833,plain,
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
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_2986,plain,
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
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_2987,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2986])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_953,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55),u1_struct_0(X3_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X1_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2005,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k3_tmap_1(sK0,X1_58,X0_58,X2_58,X0_55),u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X2_58,sK0)
    | ~ m1_pre_topc(X0_58,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_2245,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k3_tmap_1(sK0,X1_58,X0_58,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_3465,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_58))
    | v1_funct_2(k3_tmap_1(sK0,X0_58,sK0,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X0_58))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_4914,plain,
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
    inference(instantiation,[status(thm)],[c_3465])).

cnf(c_4915,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4914])).

cnf(c_8673,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5227,c_44,c_45,c_46,c_47,c_48,c_49,c_51,c_54,c_55,c_56,c_1943,c_2949,c_2987,c_4915])).

cnf(c_22,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_948,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1921,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_1947,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1921,c_926,c_947])).

cnf(c_4229,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4227,c_1947])).

cnf(c_8678,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8673,c_4229])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_949,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1920,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_1948,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1920,c_926,c_947])).

cnf(c_4230,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4227,c_1948])).

cnf(c_8677,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8673,c_4230])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8678,c_8677])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.33  % CPULimit   : 60
% 0.20/0.33  % WCLimit    : 600
% 0.20/0.33  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.20/0.33  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.89/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/0.97  
% 3.89/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.97  
% 3.89/0.97  ------  iProver source info
% 3.89/0.97  
% 3.89/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.97  git: non_committed_changes: false
% 3.89/0.97  git: last_make_outside_of_git: false
% 3.89/0.97  
% 3.89/0.97  ------ 
% 3.89/0.97  
% 3.89/0.97  ------ Input Options
% 3.89/0.97  
% 3.89/0.97  --out_options                           all
% 3.89/0.97  --tptp_safe_out                         true
% 3.89/0.97  --problem_path                          ""
% 3.89/0.97  --include_path                          ""
% 3.89/0.97  --clausifier                            res/vclausify_rel
% 3.89/0.97  --clausifier_options                    ""
% 3.89/0.97  --stdin                                 false
% 3.89/0.97  --stats_out                             all
% 3.89/0.97  
% 3.89/0.97  ------ General Options
% 3.89/0.97  
% 3.89/0.97  --fof                                   false
% 3.89/0.97  --time_out_real                         305.
% 3.89/0.97  --time_out_virtual                      -1.
% 3.89/0.97  --symbol_type_check                     false
% 3.89/0.97  --clausify_out                          false
% 3.89/0.97  --sig_cnt_out                           false
% 3.89/0.97  --trig_cnt_out                          false
% 3.89/0.97  --trig_cnt_out_tolerance                1.
% 3.89/0.97  --trig_cnt_out_sk_spl                   false
% 3.89/0.97  --abstr_cl_out                          false
% 3.89/0.97  
% 3.89/0.97  ------ Global Options
% 3.89/0.97  
% 3.89/0.97  --schedule                              default
% 3.89/0.97  --add_important_lit                     false
% 3.89/0.97  --prop_solver_per_cl                    1000
% 3.89/0.97  --min_unsat_core                        false
% 3.89/0.97  --soft_assumptions                      false
% 3.89/0.97  --soft_lemma_size                       3
% 3.89/0.97  --prop_impl_unit_size                   0
% 3.89/0.97  --prop_impl_unit                        []
% 3.89/0.97  --share_sel_clauses                     true
% 3.89/0.97  --reset_solvers                         false
% 3.89/0.97  --bc_imp_inh                            [conj_cone]
% 3.89/0.97  --conj_cone_tolerance                   3.
% 3.89/0.97  --extra_neg_conj                        none
% 3.89/0.97  --large_theory_mode                     true
% 3.89/0.97  --prolific_symb_bound                   200
% 3.89/0.97  --lt_threshold                          2000
% 3.89/0.97  --clause_weak_htbl                      true
% 3.89/0.97  --gc_record_bc_elim                     false
% 3.89/0.97  
% 3.89/0.97  ------ Preprocessing Options
% 3.89/0.97  
% 3.89/0.97  --preprocessing_flag                    true
% 3.89/0.97  --time_out_prep_mult                    0.1
% 3.89/0.97  --splitting_mode                        input
% 3.89/0.97  --splitting_grd                         true
% 3.89/0.97  --splitting_cvd                         false
% 3.89/0.97  --splitting_cvd_svl                     false
% 3.89/0.97  --splitting_nvd                         32
% 3.89/0.97  --sub_typing                            true
% 3.89/0.97  --prep_gs_sim                           true
% 3.89/0.97  --prep_unflatten                        true
% 3.89/0.97  --prep_res_sim                          true
% 3.89/0.97  --prep_upred                            true
% 3.89/0.97  --prep_sem_filter                       exhaustive
% 3.89/0.97  --prep_sem_filter_out                   false
% 3.89/0.97  --pred_elim                             true
% 3.89/0.97  --res_sim_input                         true
% 3.89/0.97  --eq_ax_congr_red                       true
% 3.89/0.97  --pure_diseq_elim                       true
% 3.89/0.97  --brand_transform                       false
% 3.89/0.97  --non_eq_to_eq                          false
% 3.89/0.97  --prep_def_merge                        true
% 3.89/0.97  --prep_def_merge_prop_impl              false
% 3.89/0.97  --prep_def_merge_mbd                    true
% 3.89/0.97  --prep_def_merge_tr_red                 false
% 3.89/0.97  --prep_def_merge_tr_cl                  false
% 3.89/0.97  --smt_preprocessing                     true
% 3.89/0.97  --smt_ac_axioms                         fast
% 3.89/0.97  --preprocessed_out                      false
% 3.89/0.97  --preprocessed_stats                    false
% 3.89/0.97  
% 3.89/0.97  ------ Abstraction refinement Options
% 3.89/0.97  
% 3.89/0.97  --abstr_ref                             []
% 3.89/0.97  --abstr_ref_prep                        false
% 3.89/0.97  --abstr_ref_until_sat                   false
% 3.89/0.97  --abstr_ref_sig_restrict                funpre
% 3.89/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.97  --abstr_ref_under                       []
% 3.89/0.97  
% 3.89/0.97  ------ SAT Options
% 3.89/0.97  
% 3.89/0.97  --sat_mode                              false
% 3.89/0.97  --sat_fm_restart_options                ""
% 3.89/0.97  --sat_gr_def                            false
% 3.89/0.97  --sat_epr_types                         true
% 3.89/0.97  --sat_non_cyclic_types                  false
% 3.89/0.97  --sat_finite_models                     false
% 3.89/0.97  --sat_fm_lemmas                         false
% 3.89/0.97  --sat_fm_prep                           false
% 3.89/0.97  --sat_fm_uc_incr                        true
% 3.89/0.97  --sat_out_model                         small
% 3.89/0.97  --sat_out_clauses                       false
% 3.89/0.97  
% 3.89/0.97  ------ QBF Options
% 3.89/0.97  
% 3.89/0.97  --qbf_mode                              false
% 3.89/0.97  --qbf_elim_univ                         false
% 3.89/0.97  --qbf_dom_inst                          none
% 3.89/0.97  --qbf_dom_pre_inst                      false
% 3.89/0.97  --qbf_sk_in                             false
% 3.89/0.97  --qbf_pred_elim                         true
% 3.89/0.97  --qbf_split                             512
% 3.89/0.97  
% 3.89/0.97  ------ BMC1 Options
% 3.89/0.97  
% 3.89/0.97  --bmc1_incremental                      false
% 3.89/0.97  --bmc1_axioms                           reachable_all
% 3.89/0.97  --bmc1_min_bound                        0
% 3.89/0.97  --bmc1_max_bound                        -1
% 3.89/0.97  --bmc1_max_bound_default                -1
% 3.89/0.97  --bmc1_symbol_reachability              true
% 3.89/0.97  --bmc1_property_lemmas                  false
% 3.89/0.97  --bmc1_k_induction                      false
% 3.89/0.97  --bmc1_non_equiv_states                 false
% 3.89/0.97  --bmc1_deadlock                         false
% 3.89/0.97  --bmc1_ucm                              false
% 3.89/0.97  --bmc1_add_unsat_core                   none
% 3.89/0.97  --bmc1_unsat_core_children              false
% 3.89/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.97  --bmc1_out_stat                         full
% 3.89/0.97  --bmc1_ground_init                      false
% 3.89/0.97  --bmc1_pre_inst_next_state              false
% 3.89/0.97  --bmc1_pre_inst_state                   false
% 3.89/0.97  --bmc1_pre_inst_reach_state             false
% 3.89/0.97  --bmc1_out_unsat_core                   false
% 3.89/0.97  --bmc1_aig_witness_out                  false
% 3.89/0.97  --bmc1_verbose                          false
% 3.89/0.97  --bmc1_dump_clauses_tptp                false
% 3.89/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.97  --bmc1_dump_file                        -
% 3.89/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.97  --bmc1_ucm_extend_mode                  1
% 3.89/0.97  --bmc1_ucm_init_mode                    2
% 3.89/0.97  --bmc1_ucm_cone_mode                    none
% 3.89/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.97  --bmc1_ucm_relax_model                  4
% 3.89/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.97  --bmc1_ucm_layered_model                none
% 3.89/0.97  --bmc1_ucm_max_lemma_size               10
% 3.89/0.97  
% 3.89/0.97  ------ AIG Options
% 3.89/0.97  
% 3.89/0.97  --aig_mode                              false
% 3.89/0.97  
% 3.89/0.97  ------ Instantiation Options
% 3.89/0.97  
% 3.89/0.97  --instantiation_flag                    true
% 3.89/0.97  --inst_sos_flag                         true
% 3.89/0.97  --inst_sos_phase                        true
% 3.89/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.97  --inst_lit_sel_side                     num_symb
% 3.89/0.97  --inst_solver_per_active                1400
% 3.89/0.97  --inst_solver_calls_frac                1.
% 3.89/0.97  --inst_passive_queue_type               priority_queues
% 3.89/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.97  --inst_passive_queues_freq              [25;2]
% 3.89/0.97  --inst_dismatching                      true
% 3.89/0.97  --inst_eager_unprocessed_to_passive     true
% 3.89/0.97  --inst_prop_sim_given                   true
% 3.89/0.97  --inst_prop_sim_new                     false
% 3.89/0.97  --inst_subs_new                         false
% 3.89/0.97  --inst_eq_res_simp                      false
% 3.89/0.97  --inst_subs_given                       false
% 3.89/0.97  --inst_orphan_elimination               true
% 3.89/0.97  --inst_learning_loop_flag               true
% 3.89/0.97  --inst_learning_start                   3000
% 3.89/0.97  --inst_learning_factor                  2
% 3.89/0.97  --inst_start_prop_sim_after_learn       3
% 3.89/0.97  --inst_sel_renew                        solver
% 3.89/0.97  --inst_lit_activity_flag                true
% 3.89/0.97  --inst_restr_to_given                   false
% 3.89/0.97  --inst_activity_threshold               500
% 3.89/0.97  --inst_out_proof                        true
% 3.89/0.97  
% 3.89/0.97  ------ Resolution Options
% 3.89/0.97  
% 3.89/0.97  --resolution_flag                       true
% 3.89/0.97  --res_lit_sel                           adaptive
% 3.89/0.97  --res_lit_sel_side                      none
% 3.89/0.97  --res_ordering                          kbo
% 3.89/0.97  --res_to_prop_solver                    active
% 3.89/0.97  --res_prop_simpl_new                    false
% 3.89/0.97  --res_prop_simpl_given                  true
% 3.89/0.97  --res_passive_queue_type                priority_queues
% 3.89/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.97  --res_passive_queues_freq               [15;5]
% 3.89/0.97  --res_forward_subs                      full
% 3.89/0.97  --res_backward_subs                     full
% 3.89/0.97  --res_forward_subs_resolution           true
% 3.89/0.97  --res_backward_subs_resolution          true
% 3.89/0.97  --res_orphan_elimination                true
% 3.89/0.97  --res_time_limit                        2.
% 3.89/0.97  --res_out_proof                         true
% 3.89/0.97  
% 3.89/0.97  ------ Superposition Options
% 3.89/0.97  
% 3.89/0.97  --superposition_flag                    true
% 3.89/0.97  --sup_passive_queue_type                priority_queues
% 3.89/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.97  --demod_completeness_check              fast
% 3.89/0.97  --demod_use_ground                      true
% 3.89/0.97  --sup_to_prop_solver                    passive
% 3.89/0.97  --sup_prop_simpl_new                    true
% 3.89/0.97  --sup_prop_simpl_given                  true
% 3.89/0.97  --sup_fun_splitting                     true
% 3.89/0.97  --sup_smt_interval                      50000
% 3.89/0.97  
% 3.89/0.97  ------ Superposition Simplification Setup
% 3.89/0.97  
% 3.89/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.89/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.89/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.89/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.89/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.89/0.97  --sup_immed_triv                        [TrivRules]
% 3.89/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_immed_bw_main                     []
% 3.89/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.89/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_input_bw                          []
% 3.89/0.97  
% 3.89/0.97  ------ Combination Options
% 3.89/0.97  
% 3.89/0.97  --comb_res_mult                         3
% 3.89/0.97  --comb_sup_mult                         2
% 3.89/0.97  --comb_inst_mult                        10
% 3.89/0.97  
% 3.89/0.97  ------ Debug Options
% 3.89/0.97  
% 3.89/0.97  --dbg_backtrace                         false
% 3.89/0.97  --dbg_dump_prop_clauses                 false
% 3.89/0.97  --dbg_dump_prop_clauses_file            -
% 3.89/0.97  --dbg_out_stat                          false
% 3.89/0.97  ------ Parsing...
% 3.89/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.97  
% 3.89/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.89/0.97  
% 3.89/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.97  
% 3.89/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.97  ------ Proving...
% 3.89/0.97  ------ Problem Properties 
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  clauses                                 40
% 3.89/0.97  conjectures                             22
% 3.89/0.97  EPR                                     18
% 3.89/0.97  Horn                                    34
% 3.89/0.97  unary                                   22
% 3.89/0.97  binary                                  3
% 3.89/0.97  lits                                    140
% 3.89/0.97  lits eq                                 6
% 3.89/0.97  fd_pure                                 0
% 3.89/0.97  fd_pseudo                               0
% 3.89/0.97  fd_cond                                 0
% 3.89/0.97  fd_pseudo_cond                          1
% 3.89/0.97  AC symbols                              0
% 3.89/0.97  
% 3.89/0.97  ------ Schedule dynamic 5 is on 
% 3.89/0.97  
% 3.89/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  ------ 
% 3.89/0.97  Current options:
% 3.89/0.97  ------ 
% 3.89/0.97  
% 3.89/0.97  ------ Input Options
% 3.89/0.97  
% 3.89/0.97  --out_options                           all
% 3.89/0.97  --tptp_safe_out                         true
% 3.89/0.97  --problem_path                          ""
% 3.89/0.97  --include_path                          ""
% 3.89/0.97  --clausifier                            res/vclausify_rel
% 3.89/0.97  --clausifier_options                    ""
% 3.89/0.97  --stdin                                 false
% 3.89/0.97  --stats_out                             all
% 3.89/0.97  
% 3.89/0.97  ------ General Options
% 3.89/0.97  
% 3.89/0.97  --fof                                   false
% 3.89/0.97  --time_out_real                         305.
% 3.89/0.97  --time_out_virtual                      -1.
% 3.89/0.97  --symbol_type_check                     false
% 3.89/0.97  --clausify_out                          false
% 3.89/0.97  --sig_cnt_out                           false
% 3.89/0.97  --trig_cnt_out                          false
% 3.89/0.97  --trig_cnt_out_tolerance                1.
% 3.89/0.97  --trig_cnt_out_sk_spl                   false
% 3.89/0.97  --abstr_cl_out                          false
% 3.89/0.97  
% 3.89/0.97  ------ Global Options
% 3.89/0.97  
% 3.89/0.97  --schedule                              default
% 3.89/0.97  --add_important_lit                     false
% 3.89/0.97  --prop_solver_per_cl                    1000
% 3.89/0.97  --min_unsat_core                        false
% 3.89/0.97  --soft_assumptions                      false
% 3.89/0.97  --soft_lemma_size                       3
% 3.89/0.97  --prop_impl_unit_size                   0
% 3.89/0.97  --prop_impl_unit                        []
% 3.89/0.97  --share_sel_clauses                     true
% 3.89/0.97  --reset_solvers                         false
% 3.89/0.97  --bc_imp_inh                            [conj_cone]
% 3.89/0.97  --conj_cone_tolerance                   3.
% 3.89/0.97  --extra_neg_conj                        none
% 3.89/0.97  --large_theory_mode                     true
% 3.89/0.97  --prolific_symb_bound                   200
% 3.89/0.97  --lt_threshold                          2000
% 3.89/0.97  --clause_weak_htbl                      true
% 3.89/0.97  --gc_record_bc_elim                     false
% 3.89/0.97  
% 3.89/0.97  ------ Preprocessing Options
% 3.89/0.97  
% 3.89/0.97  --preprocessing_flag                    true
% 3.89/0.97  --time_out_prep_mult                    0.1
% 3.89/0.97  --splitting_mode                        input
% 3.89/0.97  --splitting_grd                         true
% 3.89/0.97  --splitting_cvd                         false
% 3.89/0.97  --splitting_cvd_svl                     false
% 3.89/0.97  --splitting_nvd                         32
% 3.89/0.97  --sub_typing                            true
% 3.89/0.97  --prep_gs_sim                           true
% 3.89/0.97  --prep_unflatten                        true
% 3.89/0.97  --prep_res_sim                          true
% 3.89/0.97  --prep_upred                            true
% 3.89/0.97  --prep_sem_filter                       exhaustive
% 3.89/0.97  --prep_sem_filter_out                   false
% 3.89/0.97  --pred_elim                             true
% 3.89/0.97  --res_sim_input                         true
% 3.89/0.97  --eq_ax_congr_red                       true
% 3.89/0.97  --pure_diseq_elim                       true
% 3.89/0.97  --brand_transform                       false
% 3.89/0.97  --non_eq_to_eq                          false
% 3.89/0.97  --prep_def_merge                        true
% 3.89/0.97  --prep_def_merge_prop_impl              false
% 3.89/0.97  --prep_def_merge_mbd                    true
% 3.89/0.97  --prep_def_merge_tr_red                 false
% 3.89/0.97  --prep_def_merge_tr_cl                  false
% 3.89/0.97  --smt_preprocessing                     true
% 3.89/0.97  --smt_ac_axioms                         fast
% 3.89/0.97  --preprocessed_out                      false
% 3.89/0.97  --preprocessed_stats                    false
% 3.89/0.97  
% 3.89/0.97  ------ Abstraction refinement Options
% 3.89/0.97  
% 3.89/0.97  --abstr_ref                             []
% 3.89/0.97  --abstr_ref_prep                        false
% 3.89/0.97  --abstr_ref_until_sat                   false
% 3.89/0.97  --abstr_ref_sig_restrict                funpre
% 3.89/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.97  --abstr_ref_under                       []
% 3.89/0.97  
% 3.89/0.97  ------ SAT Options
% 3.89/0.97  
% 3.89/0.97  --sat_mode                              false
% 3.89/0.97  --sat_fm_restart_options                ""
% 3.89/0.97  --sat_gr_def                            false
% 3.89/0.97  --sat_epr_types                         true
% 3.89/0.97  --sat_non_cyclic_types                  false
% 3.89/0.97  --sat_finite_models                     false
% 3.89/0.97  --sat_fm_lemmas                         false
% 3.89/0.97  --sat_fm_prep                           false
% 3.89/0.97  --sat_fm_uc_incr                        true
% 3.89/0.97  --sat_out_model                         small
% 3.89/0.97  --sat_out_clauses                       false
% 3.89/0.97  
% 3.89/0.97  ------ QBF Options
% 3.89/0.97  
% 3.89/0.97  --qbf_mode                              false
% 3.89/0.97  --qbf_elim_univ                         false
% 3.89/0.97  --qbf_dom_inst                          none
% 3.89/0.97  --qbf_dom_pre_inst                      false
% 3.89/0.97  --qbf_sk_in                             false
% 3.89/0.97  --qbf_pred_elim                         true
% 3.89/0.97  --qbf_split                             512
% 3.89/0.97  
% 3.89/0.97  ------ BMC1 Options
% 3.89/0.97  
% 3.89/0.97  --bmc1_incremental                      false
% 3.89/0.97  --bmc1_axioms                           reachable_all
% 3.89/0.97  --bmc1_min_bound                        0
% 3.89/0.97  --bmc1_max_bound                        -1
% 3.89/0.97  --bmc1_max_bound_default                -1
% 3.89/0.97  --bmc1_symbol_reachability              true
% 3.89/0.97  --bmc1_property_lemmas                  false
% 3.89/0.97  --bmc1_k_induction                      false
% 3.89/0.97  --bmc1_non_equiv_states                 false
% 3.89/0.97  --bmc1_deadlock                         false
% 3.89/0.97  --bmc1_ucm                              false
% 3.89/0.97  --bmc1_add_unsat_core                   none
% 3.89/0.97  --bmc1_unsat_core_children              false
% 3.89/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.97  --bmc1_out_stat                         full
% 3.89/0.97  --bmc1_ground_init                      false
% 3.89/0.97  --bmc1_pre_inst_next_state              false
% 3.89/0.97  --bmc1_pre_inst_state                   false
% 3.89/0.97  --bmc1_pre_inst_reach_state             false
% 3.89/0.97  --bmc1_out_unsat_core                   false
% 3.89/0.97  --bmc1_aig_witness_out                  false
% 3.89/0.97  --bmc1_verbose                          false
% 3.89/0.97  --bmc1_dump_clauses_tptp                false
% 3.89/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.97  --bmc1_dump_file                        -
% 3.89/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.97  --bmc1_ucm_extend_mode                  1
% 3.89/0.97  --bmc1_ucm_init_mode                    2
% 3.89/0.97  --bmc1_ucm_cone_mode                    none
% 3.89/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.97  --bmc1_ucm_relax_model                  4
% 3.89/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.97  --bmc1_ucm_layered_model                none
% 3.89/0.97  --bmc1_ucm_max_lemma_size               10
% 3.89/0.97  
% 3.89/0.97  ------ AIG Options
% 3.89/0.97  
% 3.89/0.97  --aig_mode                              false
% 3.89/0.97  
% 3.89/0.97  ------ Instantiation Options
% 3.89/0.97  
% 3.89/0.97  --instantiation_flag                    true
% 3.89/0.97  --inst_sos_flag                         true
% 3.89/0.97  --inst_sos_phase                        true
% 3.89/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.97  --inst_lit_sel_side                     none
% 3.89/0.97  --inst_solver_per_active                1400
% 3.89/0.97  --inst_solver_calls_frac                1.
% 3.89/0.97  --inst_passive_queue_type               priority_queues
% 3.89/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.97  --inst_passive_queues_freq              [25;2]
% 3.89/0.97  --inst_dismatching                      true
% 3.89/0.97  --inst_eager_unprocessed_to_passive     true
% 3.89/0.97  --inst_prop_sim_given                   true
% 3.89/0.97  --inst_prop_sim_new                     false
% 3.89/0.97  --inst_subs_new                         false
% 3.89/0.97  --inst_eq_res_simp                      false
% 3.89/0.97  --inst_subs_given                       false
% 3.89/0.97  --inst_orphan_elimination               true
% 3.89/0.97  --inst_learning_loop_flag               true
% 3.89/0.97  --inst_learning_start                   3000
% 3.89/0.97  --inst_learning_factor                  2
% 3.89/0.97  --inst_start_prop_sim_after_learn       3
% 3.89/0.97  --inst_sel_renew                        solver
% 3.89/0.97  --inst_lit_activity_flag                true
% 3.89/0.97  --inst_restr_to_given                   false
% 3.89/0.97  --inst_activity_threshold               500
% 3.89/0.97  --inst_out_proof                        true
% 3.89/0.97  
% 3.89/0.97  ------ Resolution Options
% 3.89/0.97  
% 3.89/0.97  --resolution_flag                       false
% 3.89/0.97  --res_lit_sel                           adaptive
% 3.89/0.97  --res_lit_sel_side                      none
% 3.89/0.97  --res_ordering                          kbo
% 3.89/0.97  --res_to_prop_solver                    active
% 3.89/0.97  --res_prop_simpl_new                    false
% 3.89/0.97  --res_prop_simpl_given                  true
% 3.89/0.97  --res_passive_queue_type                priority_queues
% 3.89/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.97  --res_passive_queues_freq               [15;5]
% 3.89/0.97  --res_forward_subs                      full
% 3.89/0.97  --res_backward_subs                     full
% 3.89/0.97  --res_forward_subs_resolution           true
% 3.89/0.97  --res_backward_subs_resolution          true
% 3.89/0.97  --res_orphan_elimination                true
% 3.89/0.97  --res_time_limit                        2.
% 3.89/0.97  --res_out_proof                         true
% 3.89/0.97  
% 3.89/0.97  ------ Superposition Options
% 3.89/0.97  
% 3.89/0.97  --superposition_flag                    true
% 3.89/0.97  --sup_passive_queue_type                priority_queues
% 3.89/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.97  --demod_completeness_check              fast
% 3.89/0.97  --demod_use_ground                      true
% 3.89/0.97  --sup_to_prop_solver                    passive
% 3.89/0.97  --sup_prop_simpl_new                    true
% 3.89/0.97  --sup_prop_simpl_given                  true
% 3.89/0.97  --sup_fun_splitting                     true
% 3.89/0.97  --sup_smt_interval                      50000
% 3.89/0.97  
% 3.89/0.97  ------ Superposition Simplification Setup
% 3.89/0.97  
% 3.89/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.89/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.89/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.89/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.89/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.89/0.97  --sup_immed_triv                        [TrivRules]
% 3.89/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_immed_bw_main                     []
% 3.89/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.89/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.97  --sup_input_bw                          []
% 3.89/0.97  
% 3.89/0.97  ------ Combination Options
% 3.89/0.97  
% 3.89/0.97  --comb_res_mult                         3
% 3.89/0.97  --comb_sup_mult                         2
% 3.89/0.97  --comb_inst_mult                        10
% 3.89/0.97  
% 3.89/0.97  ------ Debug Options
% 3.89/0.97  
% 3.89/0.97  --dbg_backtrace                         false
% 3.89/0.97  --dbg_dump_prop_clauses                 false
% 3.89/0.97  --dbg_dump_prop_clauses_file            -
% 3.89/0.97  --dbg_out_stat                          false
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  ------ Proving...
% 3.89/0.97  
% 3.89/0.97  
% 3.89/0.97  % SZS status Theorem for theBenchmark.p
% 3.89/0.97  
% 3.89/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.97  
% 3.89/0.97  fof(f16,conjecture,(
% 3.89/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.89/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.97  
% 3.89/0.97  fof(f17,negated_conjecture,(
% 3.89/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.89/0.97    inference(negated_conjecture,[],[f16])).
% 3.89/0.97  
% 3.89/0.97  fof(f43,plain,(
% 3.89/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.89/0.97    inference(ennf_transformation,[],[f17])).
% 3.89/0.97  
% 3.89/0.97  fof(f44,plain,(
% 3.89/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.89/0.97    inference(flattening,[],[f43])).
% 3.89/0.97  
% 3.89/0.97  fof(f47,plain,(
% 3.89/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.89/0.97    inference(nnf_transformation,[],[f44])).
% 3.89/0.97  
% 3.89/0.97  fof(f48,plain,(
% 3.89/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f47])).
% 3.89/0.98  
% 3.89/0.98  fof(f55,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & X0 = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f54,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f53,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f52,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6) & sK3 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f51,plain,(
% 3.89/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f50,plain,(
% 3.89/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f49,plain,(
% 3.89/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f56,plain,(
% 3.89/0.98    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f55,f54,f53,f52,f51,f50,f49])).
% 3.89/0.98  
% 3.89/0.98  fof(f85,plain,(
% 3.89/0.98    m1_pre_topc(sK2,sK0)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f96,plain,(
% 3.89/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f10,axiom,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f31,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.89/0.98    inference(ennf_transformation,[],[f10])).
% 3.89/0.98  
% 3.89/0.98  fof(f32,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.89/0.98    inference(flattening,[],[f31])).
% 3.89/0.98  
% 3.89/0.98  fof(f46,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.89/0.98    inference(nnf_transformation,[],[f32])).
% 3.89/0.98  
% 3.89/0.98  fof(f67,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f46])).
% 3.89/0.98  
% 3.89/0.98  fof(f98,plain,(
% 3.89/0.98    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f81,plain,(
% 3.89/0.98    ~v2_struct_0(sK1)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f83,plain,(
% 3.89/0.98    l1_pre_topc(sK1)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f88,plain,(
% 3.89/0.98    v1_funct_1(sK4)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f89,plain,(
% 3.89/0.98    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f90,plain,(
% 3.89/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f94,plain,(
% 3.89/0.98    v1_funct_1(sK6)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f95,plain,(
% 3.89/0.98    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f9,axiom,(
% 3.89/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f29,plain,(
% 3.89/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f9])).
% 3.89/0.98  
% 3.89/0.98  fof(f30,plain,(
% 3.89/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f29])).
% 3.89/0.98  
% 3.89/0.98  fof(f66,plain,(
% 3.89/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f30])).
% 3.89/0.98  
% 3.89/0.98  fof(f7,axiom,(
% 3.89/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f27,plain,(
% 3.89/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f7])).
% 3.89/0.98  
% 3.89/0.98  fof(f64,plain,(
% 3.89/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f27])).
% 3.89/0.98  
% 3.89/0.98  fof(f97,plain,(
% 3.89/0.98    sK0 = sK3),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f11,axiom,(
% 3.89/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f33,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f11])).
% 3.89/0.98  
% 3.89/0.98  fof(f34,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f33])).
% 3.89/0.98  
% 3.89/0.98  fof(f69,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f34])).
% 3.89/0.98  
% 3.89/0.98  fof(f5,axiom,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f23,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.89/0.98    inference(ennf_transformation,[],[f5])).
% 3.89/0.98  
% 3.89/0.98  fof(f24,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.89/0.98    inference(flattening,[],[f23])).
% 3.89/0.98  
% 3.89/0.98  fof(f61,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f24])).
% 3.89/0.98  
% 3.89/0.98  fof(f78,plain,(
% 3.89/0.98    ~v2_struct_0(sK0)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f79,plain,(
% 3.89/0.98    v2_pre_topc(sK0)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f80,plain,(
% 3.89/0.98    l1_pre_topc(sK0)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f82,plain,(
% 3.89/0.98    v2_pre_topc(sK1)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f87,plain,(
% 3.89/0.98    m1_pre_topc(sK3,sK0)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f14,axiom,(
% 3.89/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f39,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f14])).
% 3.89/0.98  
% 3.89/0.98  fof(f40,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f39])).
% 3.89/0.98  
% 3.89/0.98  fof(f76,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f40])).
% 3.89/0.98  
% 3.89/0.98  fof(f4,axiom,(
% 3.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f18,plain,(
% 3.89/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.89/0.98    inference(pure_predicate_removal,[],[f4])).
% 3.89/0.98  
% 3.89/0.98  fof(f22,plain,(
% 3.89/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/0.98    inference(ennf_transformation,[],[f18])).
% 3.89/0.98  
% 3.89/0.98  fof(f60,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/0.98    inference(cnf_transformation,[],[f22])).
% 3.89/0.98  
% 3.89/0.98  fof(f3,axiom,(
% 3.89/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f20,plain,(
% 3.89/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.89/0.98    inference(ennf_transformation,[],[f3])).
% 3.89/0.98  
% 3.89/0.98  fof(f21,plain,(
% 3.89/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.89/0.98    inference(flattening,[],[f20])).
% 3.89/0.98  
% 3.89/0.98  fof(f59,plain,(
% 3.89/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f21])).
% 3.89/0.98  
% 3.89/0.98  fof(f2,axiom,(
% 3.89/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f58,plain,(
% 3.89/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.89/0.98    inference(cnf_transformation,[],[f2])).
% 3.89/0.98  
% 3.89/0.98  fof(f1,axiom,(
% 3.89/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f19,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f1])).
% 3.89/0.98  
% 3.89/0.98  fof(f57,plain,(
% 3.89/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f19])).
% 3.89/0.98  
% 3.89/0.98  fof(f84,plain,(
% 3.89/0.98    ~v2_struct_0(sK2)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f12,axiom,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f35,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f12])).
% 3.89/0.98  
% 3.89/0.98  fof(f36,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f35])).
% 3.89/0.98  
% 3.89/0.98  fof(f72,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f36])).
% 3.89/0.98  
% 3.89/0.98  fof(f6,axiom,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f25,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.89/0.98    inference(ennf_transformation,[],[f6])).
% 3.89/0.98  
% 3.89/0.98  fof(f26,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.89/0.98    inference(flattening,[],[f25])).
% 3.89/0.98  
% 3.89/0.98  fof(f45,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.89/0.98    inference(nnf_transformation,[],[f26])).
% 3.89/0.98  
% 3.89/0.98  fof(f62,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f45])).
% 3.89/0.98  
% 3.89/0.98  fof(f71,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f36])).
% 3.89/0.98  
% 3.89/0.98  fof(f70,plain,(
% 3.89/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f36])).
% 3.89/0.98  
% 3.89/0.98  fof(f8,axiom,(
% 3.89/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f28,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f8])).
% 3.89/0.98  
% 3.89/0.98  fof(f65,plain,(
% 3.89/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f28])).
% 3.89/0.98  
% 3.89/0.98  fof(f13,axiom,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f37,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f13])).
% 3.89/0.98  
% 3.89/0.98  fof(f38,plain,(
% 3.89/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.89/0.98    inference(flattening,[],[f37])).
% 3.89/0.98  
% 3.89/0.98  fof(f73,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f38])).
% 3.89/0.98  
% 3.89/0.98  fof(f75,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f38])).
% 3.89/0.98  
% 3.89/0.98  fof(f74,plain,(
% 3.89/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f38])).
% 3.89/0.98  
% 3.89/0.98  fof(f99,plain,(
% 3.89/0.98    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  fof(f100,plain,(
% 3.89/0.98    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 3.89/0.98    inference(cnf_transformation,[],[f56])).
% 3.89/0.98  
% 3.89/0.98  cnf(c_36,negated_conjecture,
% 3.89/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_935,negated_conjecture,
% 3.89/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_36]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1933,plain,
% 3.89/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_25,negated_conjecture,
% 3.89/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.89/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_946,negated_conjecture,
% 3.89/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1922,plain,
% 3.89/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_11,plain,
% 3.89/0.98      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.89/0.98      | ~ v1_funct_2(X5,X2,X3)
% 3.89/0.98      | ~ v1_funct_2(X4,X0,X1)
% 3.89/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.89/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.89/0.98      | v1_xboole_0(X1)
% 3.89/0.98      | v1_xboole_0(X3)
% 3.89/0.98      | ~ v1_funct_1(X5)
% 3.89/0.98      | ~ v1_funct_1(X4)
% 3.89/0.98      | X4 = X5 ),
% 3.89/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_23,negated_conjecture,
% 3.89/0.98      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
% 3.89/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_576,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.89/0.98      | ~ v1_funct_2(X3,X4,X5)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.89/0.98      | v1_xboole_0(X5)
% 3.89/0.98      | v1_xboole_0(X2)
% 3.89/0.98      | ~ v1_funct_1(X0)
% 3.89/0.98      | ~ v1_funct_1(X3)
% 3.89/0.98      | X3 = X0
% 3.89/0.98      | u1_struct_0(sK3) != X4
% 3.89/0.98      | u1_struct_0(sK0) != X1
% 3.89/0.98      | u1_struct_0(sK1) != X5
% 3.89/0.98      | u1_struct_0(sK1) != X2
% 3.89/0.98      | sK6 != X3
% 3.89/0.98      | sK4 != X0 ),
% 3.89/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_577,plain,
% 3.89/0.98      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.89/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.89/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 3.89/0.98      | ~ v1_funct_1(sK6)
% 3.89/0.98      | ~ v1_funct_1(sK4)
% 3.89/0.98      | sK6 = sK4 ),
% 3.89/0.98      inference(unflattening,[status(thm)],[c_576]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_40,negated_conjecture,
% 3.89/0.98      ( ~ v2_struct_0(sK1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_38,negated_conjecture,
% 3.89/0.98      ( l1_pre_topc(sK1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_33,negated_conjecture,
% 3.89/0.98      ( v1_funct_1(sK4) ),
% 3.89/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_32,negated_conjecture,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_31,negated_conjecture,
% 3.89/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.89/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_27,negated_conjecture,
% 3.89/0.98      ( v1_funct_1(sK6) ),
% 3.89/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_26,negated_conjecture,
% 3.89/0.98      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_9,plain,
% 3.89/0.98      ( v2_struct_0(X0)
% 3.89/0.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.89/0.98      | ~ l1_struct_0(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_98,plain,
% 3.89/0.98      ( v2_struct_0(sK1)
% 3.89/0.98      | ~ v1_xboole_0(u1_struct_0(sK1))
% 3.89/0.98      | ~ l1_struct_0(sK1) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_7,plain,
% 3.89/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_102,plain,
% 3.89/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_579,plain,
% 3.89/0.98      ( sK6 = sK4 ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_577,c_40,c_38,c_33,c_32,c_31,c_27,c_26,c_25,c_98,
% 3.89/0.98                 c_102]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_926,plain,
% 3.89/0.98      ( sK6 = sK4 ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_579]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_24,negated_conjecture,
% 3.89/0.98      ( sK0 = sK3 ),
% 3.89/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_947,negated_conjecture,
% 3.89/0.98      ( sK0 = sK3 ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1946,plain,
% 3.89/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_1922,c_926,c_947]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_12,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_pre_topc(X3,X1)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | ~ v2_pre_topc(X2)
% 3.89/0.98      | ~ v2_pre_topc(X1)
% 3.89/0.98      | v2_struct_0(X1)
% 3.89/0.98      | v2_struct_0(X2)
% 3.89/0.98      | ~ l1_pre_topc(X1)
% 3.89/0.98      | ~ l1_pre_topc(X2)
% 3.89/0.98      | ~ v1_funct_1(X0)
% 3.89/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.89/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_958,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X2_58,X0_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(X0_58)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(X0_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X0_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_55,X2_58) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1911,plain,
% 3.89/0.98      ( k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,X0_55,X2_58)
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(X1_58) != iProver_top
% 3.89/0.98      | v2_pre_topc(X0_58) != iProver_top
% 3.89/0.98      | v2_struct_0(X1_58) = iProver_top
% 3.89/0.98      | v2_struct_0(X0_58) = iProver_top
% 3.89/0.98      | l1_pre_topc(X1_58) != iProver_top
% 3.89/0.98      | l1_pre_topc(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3800,plain,
% 3.89/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_58)) = k2_tmap_1(sK0,sK1,sK4,X0_58)
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1946,c_1911]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/0.98      | ~ v1_funct_1(X0)
% 3.89/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.89/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_963,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | k2_partfun1(X0_57,X1_57,X0_55,X2_57) = k7_relat_1(X0_55,X2_57) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1906,plain,
% 3.89/0.98      ( k2_partfun1(X0_57,X1_57,X0_55,X2_57) = k7_relat_1(X0_55,X2_57)
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2638,plain,
% 3.89/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57)
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1946,c_1906]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_54,plain,
% 3.89/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2962,plain,
% 3.89/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_2638,c_54]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3802,plain,
% 3.89/0.98      ( k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58))
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_3800,c_2962]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_43,negated_conjecture,
% 3.89/0.98      ( ~ v2_struct_0(sK0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_44,plain,
% 3.89/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_42,negated_conjecture,
% 3.89/0.98      ( v2_pre_topc(sK0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_45,plain,
% 3.89/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_41,negated_conjecture,
% 3.89/0.98      ( l1_pre_topc(sK0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_46,plain,
% 3.89/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_47,plain,
% 3.89/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_39,negated_conjecture,
% 3.89/0.98      ( v2_pre_topc(sK1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_48,plain,
% 3.89/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_49,plain,
% 3.89/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_55,plain,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4221,plain,
% 3.89/0.98      ( m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58)) ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_3802,c_44,c_45,c_46,c_47,c_48,c_49,c_54,c_55]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4222,plain,
% 3.89/0.98      ( k2_tmap_1(sK0,sK1,sK4,X0_58) = k7_relat_1(sK4,u1_struct_0(X0_58))
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top ),
% 3.89/0.98      inference(renaming,[status(thm)],[c_4221]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4227,plain,
% 3.89/0.98      ( k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1933,c_4222]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_34,negated_conjecture,
% 3.89/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_937,negated_conjecture,
% 3.89/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_34]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1931,plain,
% 3.89/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1943,plain,
% 3.89/0.98      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_1931,c_947]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4228,plain,
% 3.89/0.98      ( k2_tmap_1(sK0,sK1,sK4,sK0) = k7_relat_1(sK4,u1_struct_0(sK0)) ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1943,c_4222]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_19,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 3.89/0.98      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 3.89/0.98      | ~ m1_pre_topc(X3,X2)
% 3.89/0.98      | ~ m1_pre_topc(X0,X2)
% 3.89/0.98      | ~ m1_pre_topc(X0,X3)
% 3.89/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.89/0.98      | ~ v2_pre_topc(X1)
% 3.89/0.98      | ~ v2_pre_topc(X2)
% 3.89/0.98      | v2_struct_0(X2)
% 3.89/0.98      | v2_struct_0(X1)
% 3.89/0.98      | v2_struct_0(X0)
% 3.89/0.98      | v2_struct_0(X3)
% 3.89/0.98      | ~ l1_pre_topc(X2)
% 3.89/0.98      | ~ l1_pre_topc(X1)
% 3.89/0.98      | ~ v1_funct_1(X4) ),
% 3.89/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_951,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,X3_58,X0_58,k2_tmap_1(X2_58,X1_58,X0_55,X3_58)),k2_tmap_1(X2_58,X1_58,X0_55,X0_58))
% 3.89/0.98      | ~ v1_funct_2(X0_55,u1_struct_0(X2_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X3_58,X2_58)
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X2_58)
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X3_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(X2_58)
% 3.89/0.98      | v2_struct_0(X2_58)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(X0_58)
% 3.89/0.98      | v2_struct_0(X3_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X2_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1918,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,X3_58,X0_58,k2_tmap_1(X2_58,X1_58,X0_55,X3_58)),k2_tmap_1(X2_58,X1_58,X0_55,X0_58)) = iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_pre_topc(X3_58,X2_58) != iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,X2_58) != iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,X3_58) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(X1_58) != iProver_top
% 3.89/0.98      | v2_pre_topc(X2_58) != iProver_top
% 3.89/0.98      | v2_struct_0(X2_58) = iProver_top
% 3.89/0.98      | v2_struct_0(X1_58) = iProver_top
% 3.89/0.98      | v2_struct_0(X0_58) = iProver_top
% 3.89/0.98      | v2_struct_0(X3_58) = iProver_top
% 3.89/0.98      | l1_pre_topc(X1_58) != iProver_top
% 3.89/0.98      | l1_pre_topc(X2_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4339,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(X0_58) = iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4228,c_1918]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_56,plain,
% 3.89/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5204,plain,
% 3.89/0.98      ( v2_struct_0(X0_58) = iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_4339,c_44,c_45,c_46,c_47,c_48,c_49,c_54,c_55,c_56,
% 3.89/0.98                 c_1943]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5205,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,k7_relat_1(sK4,u1_struct_0(sK0))),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | v2_struct_0(X0_58) = iProver_top ),
% 3.89/0.98      inference(renaming,[status(thm)],[c_5204]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3,plain,
% 3.89/0.98      ( v4_relat_1(X0,X1)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.89/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2,plain,
% 3.89/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.89/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_556,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/0.98      | ~ v1_relat_1(X0)
% 3.89/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.89/0.98      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_927,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.89/0.98      | ~ v1_relat_1(X0_55)
% 3.89/0.98      | k7_relat_1(X0_55,X0_57) = X0_55 ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_556]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1941,plain,
% 3.89/0.98      ( k7_relat_1(X0_55,X0_57) = X0_55
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.89/0.98      | v1_relat_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4359,plain,
% 3.89/0.98      ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4
% 3.89/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1946,c_1941]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1,plain,
% 3.89/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_964,plain,
% 3.89/0.98      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1905,plain,
% 3.89/0.98      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_0,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/0.98      | ~ v1_relat_1(X1)
% 3.89/0.98      | v1_relat_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_965,plain,
% 3.89/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 3.89/0.98      | ~ v1_relat_1(X1_55)
% 3.89/0.98      | v1_relat_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1904,plain,
% 3.89/0.98      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 3.89/0.98      | v1_relat_1(X1_55) != iProver_top
% 3.89/0.98      | v1_relat_1(X0_55) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2420,plain,
% 3.89/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.89/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1946,c_1904]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2851,plain,
% 3.89/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1905,c_2420]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4451,plain,
% 3.89/0.98      ( k7_relat_1(sK4,u1_struct_0(sK0)) = sK4 ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_4359,c_2851]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5210,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(X0_58),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_58,sK4),k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
% 3.89/0.98      | m1_pre_topc(X0_58,sK0) != iProver_top
% 3.89/0.98      | v2_struct_0(X0_58) = iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_5205,c_4451]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5214,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top
% 3.89/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.89/0.98      | v2_struct_0(sK2) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4227,c_5210]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_37,negated_conjecture,
% 3.89/0.98      ( ~ v2_struct_0(sK2) ),
% 3.89/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_50,plain,
% 3.89/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_51,plain,
% 3.89/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5223,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_5214,c_50,c_51]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.89/0.98      | ~ l1_struct_0(X1)
% 3.89/0.98      | ~ l1_struct_0(X2)
% 3.89/0.98      | ~ l1_struct_0(X3)
% 3.89/0.98      | ~ v1_funct_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_957,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ l1_struct_0(X1_58)
% 3.89/0.98      | ~ l1_struct_0(X2_58)
% 3.89/0.98      | ~ l1_struct_0(X0_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1912,plain,
% 3.89/0.98      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | m1_subset_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) = iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_957]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_6,plain,
% 3.89/0.98      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.89/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.89/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.89/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.89/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.89/0.98      | ~ v1_funct_1(X2)
% 3.89/0.98      | ~ v1_funct_1(X3)
% 3.89/0.98      | X3 = X2 ),
% 3.89/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_961,plain,
% 3.89/0.98      ( ~ r2_funct_2(X0_57,X1_57,X0_55,X1_55)
% 3.89/0.98      | ~ v1_funct_2(X1_55,X0_57,X1_57)
% 3.89/0.98      | ~ v1_funct_2(X0_55,X0_57,X1_57)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.89/0.98      | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | ~ v1_funct_1(X1_55)
% 3.89/0.98      | X1_55 = X0_55 ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1908,plain,
% 3.89/0.98      ( X0_55 = X1_55
% 3.89/0.98      | r2_funct_2(X0_57,X1_57,X1_55,X0_55) != iProver_top
% 3.89/0.98      | v1_funct_2(X1_55,X0_57,X1_57) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,X0_57,X1_57) != iProver_top
% 3.89/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.89/0.98      | v1_funct_1(X1_55) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3341,plain,
% 3.89/0.98      ( k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(X1_55) != iProver_top
% 3.89/0.98      | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1912,c_1908]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_14,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | ~ l1_struct_0(X1)
% 3.89/0.98      | ~ l1_struct_0(X2)
% 3.89/0.98      | ~ l1_struct_0(X3)
% 3.89/0.98      | ~ v1_funct_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_956,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ l1_struct_0(X1_58)
% 3.89/0.98      | ~ l1_struct_0(X2_58)
% 3.89/0.98      | ~ l1_struct_0(X0_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1027,plain,
% 3.89/0.98      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_15,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | ~ l1_struct_0(X1)
% 3.89/0.98      | ~ l1_struct_0(X2)
% 3.89/0.98      | ~ l1_struct_0(X3)
% 3.89/0.98      | ~ v1_funct_1(X0)
% 3.89/0.98      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_955,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ l1_struct_0(X1_58)
% 3.89/0.98      | ~ l1_struct_0(X2_58)
% 3.89/0.98      | ~ l1_struct_0(X0_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1030,plain,
% 3.89/0.98      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4843,plain,
% 3.89/0.98      ( v1_funct_1(X1_55) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_3341,c_1027,c_1030]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4844,plain,
% 3.89/0.98      ( k2_tmap_1(X0_58,X1_58,X0_55,X2_58) = X1_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),X1_55,k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(X1_55,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(X1_55) != iProver_top ),
% 3.89/0.98      inference(renaming,[status(thm)],[c_4843]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4850,plain,
% 3.89/0.98      ( k2_tmap_1(sK0,sK1,sK4,sK2) = X0_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | l1_struct_0(sK0) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) != iProver_top
% 3.89/0.98      | l1_struct_0(sK2) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4227,c_4844]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4853,plain,
% 3.89/0.98      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | l1_struct_0(sK0) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) != iProver_top
% 3.89/0.98      | l1_struct_0(sK2) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_4850,c_4227]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_101,plain,
% 3.89/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_103,plain,
% 3.89/0.98      ( l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) = iProver_top ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_101]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_930,negated_conjecture,
% 3.89/0.98      ( l1_pre_topc(sK0) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_41]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1938,plain,
% 3.89/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_960,plain,
% 3.89/0.98      ( ~ l1_pre_topc(X0_58) | l1_struct_0(X0_58) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1909,plain,
% 3.89/0.98      ( l1_pre_topc(X0_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2587,plain,
% 3.89/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1938,c_1909]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_8,plain,
% 3.89/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_959,plain,
% 3.89/0.98      ( ~ m1_pre_topc(X0_58,X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | l1_pre_topc(X0_58) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1910,plain,
% 3.89/0.98      ( m1_pre_topc(X0_58,X1_58) != iProver_top
% 3.89/0.98      | l1_pre_topc(X1_58) != iProver_top
% 3.89/0.98      | l1_pre_topc(X0_58) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2591,plain,
% 3.89/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1933,c_1910]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2844,plain,
% 3.89/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_2591,c_46]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2848,plain,
% 3.89/0.98      ( l1_struct_0(sK2) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_2844,c_1909]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1913,plain,
% 3.89/0.98      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | v1_funct_2(k2_tmap_1(X0_58,X1_58,X0_55,X2_58),u1_struct_0(X2_58),u1_struct_0(X1_58)) = iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4236,plain,
% 3.89/0.98      ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | l1_struct_0(sK0) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) != iProver_top
% 3.89/0.98      | l1_struct_0(sK2) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4227,c_1913]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1914,plain,
% 3.89/0.98      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 3.89/0.98      | l1_struct_0(X1_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X2_58) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(k2_tmap_1(X0_58,X1_58,X0_55,X2_58)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3233,plain,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | l1_struct_0(sK0) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1946,c_1914]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3441,plain,
% 3.89/0.98      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top
% 3.89/0.98      | l1_struct_0(X0_58) != iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_3233,c_49,c_54,c_55,c_103,c_2587]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3442,plain,
% 3.89/0.98      ( l1_struct_0(X0_58) != iProver_top
% 3.89/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_58)) = iProver_top ),
% 3.89/0.98      inference(renaming,[status(thm)],[c_3441]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4237,plain,
% 3.89/0.98      ( l1_struct_0(sK2) != iProver_top
% 3.89/0.98      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) = iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4227,c_3442]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4235,plain,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | l1_struct_0(sK0) != iProver_top
% 3.89/0.98      | l1_struct_0(sK1) != iProver_top
% 3.89/0.98      | l1_struct_0(sK2) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4227,c_1912]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4782,plain,
% 3.89/0.98      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_4235,c_49,c_54,c_55,c_56,c_103,c_2587,c_2848]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4787,plain,
% 3.89/0.98      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_4782,c_1908]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5108,plain,
% 3.89/0.98      ( v1_funct_1(X0_55) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_4853,c_49,c_54,c_55,c_56,c_103,c_2587,c_2848,c_4236,
% 3.89/0.98                 c_4237,c_4787]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5109,plain,
% 3.89/0.98      ( k7_relat_1(sK4,u1_struct_0(sK2)) = X0_55
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_55,k7_relat_1(sK4,u1_struct_0(sK2))) != iProver_top
% 3.89/0.98      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.89/0.98      inference(renaming,[status(thm)],[c_5108]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_5227,plain,
% 3.89/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_5223,c_5109]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_18,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_pre_topc(X3,X4)
% 3.89/0.98      | ~ m1_pre_topc(X1,X4)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | ~ v2_pre_topc(X2)
% 3.89/0.98      | ~ v2_pre_topc(X4)
% 3.89/0.98      | v2_struct_0(X4)
% 3.89/0.98      | v2_struct_0(X2)
% 3.89/0.98      | ~ l1_pre_topc(X4)
% 3.89/0.98      | ~ l1_pre_topc(X2)
% 3.89/0.98      | ~ v1_funct_1(X0)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_952,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X2_58)
% 3.89/0.98      | ~ m1_pre_topc(X3_58,X2_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(X2_58)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(X2_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X2_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55)) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2040,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X1_58)
% 3.89/0.98      | ~ m1_pre_topc(X2_58,X1_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(X1_58,sK1,X0_58,X2_58,X0_55)) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_952]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2499,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0_58,X0_55)) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2040]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2803,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55)) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2499]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2948,plain,
% 3.89/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
% 3.89/0.98      | ~ v1_funct_1(sK4) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2803]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2949,plain,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) = iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_2948]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_16,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_pre_topc(X3,X4)
% 3.89/0.98      | ~ m1_pre_topc(X1,X4)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.89/0.98      | ~ v2_pre_topc(X2)
% 3.89/0.98      | ~ v2_pre_topc(X4)
% 3.89/0.98      | v2_struct_0(X4)
% 3.89/0.98      | v2_struct_0(X2)
% 3.89/0.98      | ~ l1_pre_topc(X4)
% 3.89/0.98      | ~ l1_pre_topc(X2)
% 3.89/0.98      | ~ v1_funct_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_954,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X2_58)
% 3.89/0.98      | ~ m1_pre_topc(X3_58,X2_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | m1_subset_1(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(X2_58)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(X2_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X2_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2038,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X1_58)
% 3.89/0.98      | ~ m1_pre_topc(X2_58,X1_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
% 3.89/0.98      | m1_subset_1(k3_tmap_1(X1_58,sK1,X0_58,X2_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_954]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2497,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0_58,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2038]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2833,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2497]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2986,plain,
% 3.89/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.89/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(sK4) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2833]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2987,plain,
% 3.89/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.89/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_2986]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_17,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.89/0.98      | ~ m1_pre_topc(X4,X3)
% 3.89/0.98      | ~ m1_pre_topc(X1,X3)
% 3.89/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.89/0.98      | ~ v2_pre_topc(X2)
% 3.89/0.98      | ~ v2_pre_topc(X3)
% 3.89/0.98      | v2_struct_0(X3)
% 3.89/0.98      | v2_struct_0(X2)
% 3.89/0.98      | ~ l1_pre_topc(X3)
% 3.89/0.98      | ~ l1_pre_topc(X2)
% 3.89/0.98      | ~ v1_funct_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_953,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_55),u1_struct_0(X3_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X3_58,X2_58)
% 3.89/0.98      | ~ m1_pre_topc(X0_58,X2_58)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(X2_58)
% 3.89/0.98      | v2_struct_0(X2_58)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(X2_58)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2005,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(sK0,X1_58,X0_58,X2_58,X0_55),u1_struct_0(X2_58),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X2_58,sK0)
% 3.89/0.98      | ~ m1_pre_topc(X0_58,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_953]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2245,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(sK0,X1_58,X0_58,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X1_58))
% 3.89/0.98      | ~ m1_pre_topc(X0_58,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 3.89/0.98      | ~ v2_pre_topc(X1_58)
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | v2_struct_0(X1_58)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | ~ l1_pre_topc(X1_58)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2005]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3465,plain,
% 3.89/0.98      ( ~ v1_funct_2(X0_55,u1_struct_0(sK0),u1_struct_0(X0_58))
% 3.89/0.98      | v1_funct_2(k3_tmap_1(sK0,X0_58,sK0,sK2,X0_55),u1_struct_0(sK2),u1_struct_0(X0_58))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_58))))
% 3.89/0.98      | ~ v2_pre_topc(X0_58)
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | v2_struct_0(X0_58)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | ~ l1_pre_topc(X0_58)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ v1_funct_1(X0_55) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_2245]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4914,plain,
% 3.89/0.98      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.89/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.89/0.98      | ~ m1_pre_topc(sK0,sK0)
% 3.89/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.89/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.89/0.98      | ~ v2_pre_topc(sK0)
% 3.89/0.98      | ~ v2_pre_topc(sK1)
% 3.89/0.98      | v2_struct_0(sK0)
% 3.89/0.98      | v2_struct_0(sK1)
% 3.89/0.98      | ~ l1_pre_topc(sK0)
% 3.89/0.98      | ~ l1_pre_topc(sK1)
% 3.89/0.98      | ~ v1_funct_1(sK4) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_3465]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4915,plain,
% 3.89/0.98      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 3.89/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.89/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.89/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.89/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v2_struct_0(sK0) = iProver_top
% 3.89/0.98      | v2_struct_0(sK1) = iProver_top
% 3.89/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.89/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_4914]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_8673,plain,
% 3.89/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_5227,c_44,c_45,c_46,c_47,c_48,c_49,c_51,c_54,c_55,
% 3.89/0.98                 c_56,c_1943,c_2949,c_2987,c_4915]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_22,negated_conjecture,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 3.89/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_948,negated_conjecture,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1921,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1947,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_1921,c_926,c_947]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4229,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_4227,c_1947]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_8678,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_8673,c_4229]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_21,negated_conjecture,
% 3.89/0.98      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 3.89/0.98      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 3.89/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_949,negated_conjecture,
% 3.89/0.98      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 3.89/0.98      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 3.89/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1920,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1948,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_1920,c_926,c_947]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4230,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 3.89/0.98      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_4227,c_1948]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_8677,plain,
% 3.89/0.98      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != iProver_top ),
% 3.89/0.98      inference(demodulation,[status(thm)],[c_8673,c_4230]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(contradiction,plain,
% 3.89/0.98      ( $false ),
% 3.89/0.98      inference(minisat,[status(thm)],[c_8678,c_8677]) ).
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.98  
% 3.89/0.98  ------                               Statistics
% 3.89/0.98  
% 3.89/0.98  ------ General
% 3.89/0.98  
% 3.89/0.98  abstr_ref_over_cycles:                  0
% 3.89/0.98  abstr_ref_under_cycles:                 0
% 3.89/0.98  gc_basic_clause_elim:                   0
% 3.89/0.98  forced_gc_time:                         0
% 3.89/0.98  parsing_time:                           0.019
% 3.89/0.98  unif_index_cands_time:                  0.
% 3.89/0.98  unif_index_add_time:                    0.
% 3.89/0.98  orderings_time:                         0.
% 3.89/0.98  out_proof_time:                         0.021
% 3.89/0.98  total_time:                             0.452
% 3.89/0.98  num_of_symbols:                         59
% 3.89/0.98  num_of_terms:                           11843
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing
% 3.89/0.98  
% 3.89/0.98  num_of_splits:                          0
% 3.89/0.98  num_of_split_atoms:                     0
% 3.89/0.98  num_of_reused_defs:                     0
% 3.89/0.98  num_eq_ax_congr_red:                    14
% 3.89/0.98  num_of_sem_filtered_clauses:            1
% 3.89/0.98  num_of_subtypes:                        4
% 3.89/0.98  monotx_restored_types:                  0
% 3.89/0.98  sat_num_of_epr_types:                   0
% 3.89/0.98  sat_num_of_non_cyclic_types:            0
% 3.89/0.98  sat_guarded_non_collapsed_types:        1
% 3.89/0.98  num_pure_diseq_elim:                    0
% 3.89/0.98  simp_replaced_by:                       0
% 3.89/0.98  res_preprocessed:                       207
% 3.89/0.98  prep_upred:                             0
% 3.89/0.98  prep_unflattend:                        12
% 3.89/0.98  smt_new_axioms:                         0
% 3.89/0.98  pred_elim_cands:                        10
% 3.89/0.98  pred_elim:                              3
% 3.89/0.98  pred_elim_cl:                           4
% 3.89/0.98  pred_elim_cycles:                       5
% 3.89/0.98  merged_defs:                            8
% 3.89/0.98  merged_defs_ncl:                        0
% 3.89/0.98  bin_hyper_res:                          8
% 3.89/0.98  prep_cycles:                            4
% 3.89/0.98  pred_elim_time:                         0.004
% 3.89/0.98  splitting_time:                         0.
% 3.89/0.98  sem_filter_time:                        0.
% 3.89/0.98  monotx_time:                            0.
% 3.89/0.98  subtype_inf_time:                       0.001
% 3.89/0.98  
% 3.89/0.98  ------ Problem properties
% 3.89/0.98  
% 3.89/0.98  clauses:                                40
% 3.89/0.98  conjectures:                            22
% 3.89/0.98  epr:                                    18
% 3.89/0.98  horn:                                   34
% 3.89/0.98  ground:                                 23
% 3.89/0.98  unary:                                  22
% 3.89/0.98  binary:                                 3
% 3.89/0.98  lits:                                   140
% 3.89/0.98  lits_eq:                                6
% 3.89/0.98  fd_pure:                                0
% 3.89/0.98  fd_pseudo:                              0
% 3.89/0.98  fd_cond:                                0
% 3.89/0.98  fd_pseudo_cond:                         1
% 3.89/0.98  ac_symbols:                             0
% 3.89/0.98  
% 3.89/0.98  ------ Propositional Solver
% 3.89/0.98  
% 3.89/0.98  prop_solver_calls:                      32
% 3.89/0.98  prop_fast_solver_calls:                 2241
% 3.89/0.98  smt_solver_calls:                       0
% 3.89/0.98  smt_fast_solver_calls:                  0
% 3.89/0.98  prop_num_of_clauses:                    4284
% 3.89/0.98  prop_preprocess_simplified:             9808
% 3.89/0.98  prop_fo_subsumed:                       222
% 3.89/0.98  prop_solver_time:                       0.
% 3.89/0.98  smt_solver_time:                        0.
% 3.89/0.98  smt_fast_solver_time:                   0.
% 3.89/0.98  prop_fast_solver_time:                  0.
% 3.89/0.98  prop_unsat_core_time:                   0.001
% 3.89/0.98  
% 3.89/0.98  ------ QBF
% 3.89/0.98  
% 3.89/0.98  qbf_q_res:                              0
% 3.89/0.98  qbf_num_tautologies:                    0
% 3.89/0.98  qbf_prep_cycles:                        0
% 3.89/0.98  
% 3.89/0.98  ------ BMC1
% 3.89/0.98  
% 3.89/0.98  bmc1_current_bound:                     -1
% 3.89/0.98  bmc1_last_solved_bound:                 -1
% 3.89/0.98  bmc1_unsat_core_size:                   -1
% 3.89/0.98  bmc1_unsat_core_parents_size:           -1
% 3.89/0.98  bmc1_merge_next_fun:                    0
% 3.89/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.89/0.98  
% 3.89/0.98  ------ Instantiation
% 3.89/0.98  
% 3.89/0.98  inst_num_of_clauses:                    1255
% 3.89/0.98  inst_num_in_passive:                    311
% 3.89/0.98  inst_num_in_active:                     500
% 3.89/0.98  inst_num_in_unprocessed:                444
% 3.89/0.98  inst_num_of_loops:                      580
% 3.89/0.98  inst_num_of_learning_restarts:          0
% 3.89/0.98  inst_num_moves_active_passive:          74
% 3.89/0.98  inst_lit_activity:                      0
% 3.89/0.98  inst_lit_activity_moves:                0
% 3.89/0.98  inst_num_tautologies:                   0
% 3.89/0.98  inst_num_prop_implied:                  0
% 3.89/0.98  inst_num_existing_simplified:           0
% 3.89/0.98  inst_num_eq_res_simplified:             0
% 3.89/0.98  inst_num_child_elim:                    0
% 3.89/0.98  inst_num_of_dismatching_blockings:      100
% 3.89/0.98  inst_num_of_non_proper_insts:           1019
% 3.89/0.98  inst_num_of_duplicates:                 0
% 3.89/0.98  inst_inst_num_from_inst_to_res:         0
% 3.89/0.98  inst_dismatching_checking_time:         0.
% 3.89/0.98  
% 3.89/0.98  ------ Resolution
% 3.89/0.98  
% 3.89/0.98  res_num_of_clauses:                     0
% 3.89/0.98  res_num_in_passive:                     0
% 3.89/0.98  res_num_in_active:                      0
% 3.89/0.98  res_num_of_loops:                       211
% 3.89/0.98  res_forward_subset_subsumed:            47
% 3.89/0.98  res_backward_subset_subsumed:           0
% 3.89/0.98  res_forward_subsumed:                   0
% 3.89/0.98  res_backward_subsumed:                  0
% 3.89/0.98  res_forward_subsumption_resolution:     0
% 3.89/0.98  res_backward_subsumption_resolution:    0
% 3.89/0.98  res_clause_to_clause_subsumption:       295
% 3.89/0.98  res_orphan_elimination:                 0
% 3.89/0.98  res_tautology_del:                      59
% 3.89/0.98  res_num_eq_res_simplified:              0
% 3.89/0.98  res_num_sel_changes:                    0
% 3.89/0.98  res_moves_from_active_to_pass:          0
% 3.89/0.98  
% 3.89/0.98  ------ Superposition
% 3.89/0.98  
% 3.89/0.98  sup_time_total:                         0.
% 3.89/0.98  sup_time_generating:                    0.
% 3.89/0.98  sup_time_sim_full:                      0.
% 3.89/0.98  sup_time_sim_immed:                     0.
% 3.89/0.98  
% 3.89/0.98  sup_num_of_clauses:                     139
% 3.89/0.98  sup_num_in_active:                      102
% 3.89/0.98  sup_num_in_passive:                     37
% 3.89/0.98  sup_num_of_loops:                       114
% 3.89/0.98  sup_fw_superposition:                   90
% 3.89/0.98  sup_bw_superposition:                   53
% 3.89/0.98  sup_immediate_simplified:               25
% 3.89/0.98  sup_given_eliminated:                   0
% 3.89/0.98  comparisons_done:                       0
% 3.89/0.98  comparisons_avoided:                    0
% 3.89/0.98  
% 3.89/0.98  ------ Simplifications
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  sim_fw_subset_subsumed:                 9
% 3.89/0.98  sim_bw_subset_subsumed:                 10
% 3.89/0.98  sim_fw_subsumed:                        4
% 3.89/0.98  sim_bw_subsumed:                        2
% 3.89/0.98  sim_fw_subsumption_res:                 0
% 3.89/0.98  sim_bw_subsumption_res:                 0
% 3.89/0.98  sim_tautology_del:                      6
% 3.89/0.98  sim_eq_tautology_del:                   7
% 3.89/0.98  sim_eq_res_simp:                        0
% 3.89/0.98  sim_fw_demodulated:                     7
% 3.89/0.98  sim_bw_demodulated:                     7
% 3.89/0.98  sim_light_normalised:                   18
% 3.89/0.98  sim_joinable_taut:                      0
% 3.89/0.98  sim_joinable_simp:                      0
% 3.89/0.98  sim_ac_normalised:                      0
% 3.89/0.98  sim_smt_subsumption:                    0
% 3.89/0.98  
%------------------------------------------------------------------------------
